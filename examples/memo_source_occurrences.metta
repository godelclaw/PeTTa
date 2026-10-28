!(import! &self (library lib_memo))

; Enabling a cache preserves source order and duplicate equation occurrences.
(= (memo-occurrence-all) z)
(= (memo-occurrence-all) a)
(= (memo-occurrence-all) z)
!(test (collapse (memo-occurrence-all)) (z a z))
!(memoize memo-occurrence-all)
!(test (collapse (memo-occurrence-all)) (z a z))
!(test (collapse (memo-occurrence-all)) (z a z))

(= (memo-occurrence-arity) z)
(= (memo-occurrence-arity) a)
(= (memo-occurrence-arity) z)
!(test (collapse (memo-occurrence-arity)) (z a z))
!(memoize memo-occurrence-arity 0)
!(test (collapse (memo-occurrence-arity)) (z a z))
!(test (collapse (memo-occurrence-arity)) (z a z))
