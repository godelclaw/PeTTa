"""Compare runtime contracts with a separate baseline checkout.

Run in the same SWI/Janus environment as test.sh. Requires GNU time.
Microbenchmarks use compiled MeTTa calls, including legacy call-site guards.
Typed workloads keep the same declarations on both checkouts. Untyped workloads
are separate regression gates. Heavy workloads include loading and assertions.
"""
import argparse
import hashlib
import json
import re
import statistics
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
PROGRAMS = {
    "small": ("Number Number", "(= (bf $x) (+ $x 1))"),
    "count": ("Number Number Number", "(= (bf $n $a) (if (== $n 0) $a (bf (- $n 1) (+ $a 1))))"),
    "relation": ("Number Number Number", "(= (bf 0 $x) $x) (= (bf $n $x) (if (> $n 0) (bf (- $n 1) $x) (empty)))"),
    "list": ("BenchChain Number", "(= (bf Nil) 0) (= (bf (Cons $h $t)) (+ 1 (bf $t)))"),
}
CONSTRUCTORS = "(: BenchChain Type) (: Nil BenchChain) (: Cons (-> Number BenchChain BenchChain))\n"


def source_state(root):
    rev = subprocess.check_output(["git", "rev-parse", "HEAD"], cwd=root, text=True).strip()
    files = [*root.joinpath("src").rglob("*.pl"), *root.joinpath("lib").rglob("*")]
    hashes = {str(p.relative_to(root)): hashlib.sha256(p.read_bytes()).hexdigest()
              for p in files if p.is_file()}
    return {"revision": rev, "sha256": hashes}


def invoke(root, args, entry, timeout):
    cmd = ["/usr/bin/time", "-f", "RSS=%M", "nice", "-n", "19", "swipl", "-q",
           "-s", str(root / "src/metta.pl"), "-s", str(ROOT / "tests/bench_runtime_types.pl"),
           "-g", entry, "-t", "halt", "--", *map(str, args), "--silent"]
    r = subprocess.run(cmd, cwd=root, text=True, capture_output=True, timeout=timeout)
    if r.returncode or "❌" in r.stdout or re.search(r"^ERROR:", r.stderr, re.M):
        raise RuntimeError((root.name, args, r.returncode, r.stdout[-1200:], r.stderr[-1200:]))
    data = json.loads(r.stdout.rsplit("MEASURE=", 1)[-1])
    data["rss_kib"] = int(re.search(r"RSS=(\d+)", r.stderr)[1])
    return data


def main():
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument("--baseline", type=Path, required=True)
    ap.add_argument("--output", type=Path, required=True, help="Result directory")
    ap.add_argument("--repeats", type=int, default=3)
    ap.add_argument("--timeout", type=int, default=120)
    ap.add_argument("--heavy", nargs="*", default=["he_minimalmetta", "holbenchmark", "nars_tuffy", "tilepuzzle", "nilbc"])
    args = ap.parse_args()
    if args.repeats < 1:
        ap.error("--repeats must be positive")
    dest = args.output.resolve()
    dest.mkdir(parents=True, exist_ok=True)
    roots = [("stable", args.baseline.resolve()), ("candidate", ROOT)]
    state = {label: source_state(root) for label, root in roots}
    report = {"sources": state, "route": "compiled_metta_call", "cases": []}

    def save():
        (dest / "results.json").write_text(json.dumps(report, indent=2) + "\n")

    cases = [(k, n, t) for k, n in [("small", 10000), ("count", 200000), ("list", 400), ("relation", 10000)] for t in [False, True]]
    cases += [("heavy:" + name, 0, False) for name in args.heavy]
    for kind, n, typed in cases:
        row = {"kind": kind, "n": n, "typed": typed, "runs": {label: [] for label, _ in roots}}
        for repeat in range(args.repeats):
            for label, root in (roots if repeat % 2 == 0 else roots[::-1]):
                if kind.startswith("heavy:"):
                    run = invoke(root, [root / "examples" / (kind[6:] + ".metta")], "runtime_heavy_main", args.timeout)
                else:
                    sig, body = PROGRAMS[kind]
                    source = dest / (kind + ("-typed" if typed else "-untyped") + ".metta")
                    source.write_text(CONSTRUCTORS + ("(: bf (-> " + sig + "))\n" if typed else "") + body + "\n")
                    run = invoke(root, [source, kind, n], "runtime_bench_main", args.timeout)
                row["runs"][label].append(run)
        row["medians"] = {label: {k: statistics.median(r[k] for r in runs) for k in ["cpu", "inferences", "rss_kib"]}
                          for label, runs in row["runs"].items()}
        report["cases"].append(row)
        save()
        print(kind, n, typed, row["medians"], flush=True)

    report["untyped_gates"] = {label: invoke(root, [], "runtime_untyped_main", args.timeout) for label, root in roots}
    report["sources_unchanged"] = all(source_state(root) == state[label] for label, root in roots)
    gates = report["untyped_gates"]
    report["untyped_inferences_match"] = (
        [x["inferences"] for x in gates["stable"]["rows"]] == [x["inferences"] for x in gates["candidate"]["rows"]]
        and all(row["medians"]["stable"]["inferences"] == row["medians"]["candidate"]["inferences"]
                for row in report["cases"] if not row["typed"] and not row["kind"].startswith("heavy:")))
    save()
    if not report["sources_unchanged"] or not report["untyped_inferences_match"]:
        raise SystemExit("Source changed during measurement or an untyped inference gate failed")
    print("Untyped inference gates pass; source hashes unchanged.", flush=True)


if __name__ == "__main__":
    main()
