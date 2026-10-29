; memoize! recompiles a function's clauses where they are: no row moves, none is
; lost or duplicated, and a definition in another space stays there.
!(import! &self (library lib_memo))

(= (mf 1 0) 99)
(= (mf $x 0) 99)
(= (mf 0 $y) 99)
!(test (collapse (mf 0 5)) (99))
!(test (collapse (memoize mf)) (True))
!(test (collapse (mf 0 5)) (99))
!(test (size-atom (collapse (match &self (= (mf $a $b) $c) $c))) 3)

; Duplicated equations stay duplicated, in their order, and cache their answers:
!(bind! &md-runs (new-state 0))
(= (md 1) (progn (change-state! &md-runs (+ 1 (get-state &md-runs))) a))
(= (md 1) (progn (change-state! &md-runs (+ 1 (get-state &md-runs))) b))
(= (md 1) (progn (change-state! &md-runs (+ 1 (get-state &md-runs))) a))
!(memoize md)
!(test (collapse (md 1)) (a b a))
!(test (collapse (md 1)) (a b a))
!(test (get-state &md-runs) 3)

; A definition in another space stays there, keeps its clause, and caches too:
!(bind! &mo-runs (new-state 0))
(= (mo 1) (progn (change-state! &mo-runs (+ 1 (get-state &mo-runs))) self))
!(add-atom &other (= (mo 1) (progn (change-state! &mo-runs (+ 1 (get-state &mo-runs))) other)))
!(memoize mo)
!(test (collapse (mo 1)) (self other))
!(test (collapse (mo 1)) (self other))
!(test (get-state &mo-runs) 2)
!(test (size-atom (collapse (match &self (= (mo 1) $v) $v))) 1)
!(test (size-atom (collapse (match &other (= (mo 1) $v) $v))) 1)

; A recursive function defined only in another space stays only there (0 in &self):
!(bind! &ofib-runs (new-state 0))
!(add-atom &other (= (ofib $n)
   (progn (change-state! &ofib-runs (+ 1 (get-state &ofib-runs)))
          (if (< $n 2) $n (+ (ofib (- $n 1)) (ofib (- $n 2)))))))
!(memoize ofib)
!(test (ofib 10) 55)
!(test (get-state &ofib-runs) 11)
!(test (size-atom (collapse (match &self (= (ofib $a) $b) $a))) 0)
!(test (size-atom (collapse (match &other (= (ofib $a) $b) $a))) 1)

; One arity can be memoized alone:
!(bind! &ma-runs (new-state 0))
(= (ma $x) (progn (change-state! &ma-runs (+ 1 (get-state &ma-runs))) (+ $x 1)))
(= (ma $x $y) (progn (change-state! &ma-runs (+ 1 (get-state &ma-runs))) (+ $x $y)))
!(memoize ma 1)
!(test (ma 1) 2)
!(test (ma 1) 2)
!(test (get-state &ma-runs) 1)
!(test (ma 1 2) 3)
!(test (ma 1 2) 3)
!(test (get-state &ma-runs) 3)

; A definition whose variables compiling could alias keeps its unaliased row:
(= (ident-memo $a $b)
   (if True
       (let red $a $a)
       (let blue $b $b)))
!(memoize ident-memo)
!(test (collapse (ident-memo red red)) (red))
!(test (size-atom (collapse (match &self (= (ident-memo red green) $body) $body))) 1)

; Functions sharing names with Prolog built-ins of other arities memoize cleanly:
!(bind! &sys-runs (new-state 0))
(= (plus $x) (progn (change-state! &sys-runs (+ 1 (get-state &sys-runs))) (+ $x 10)))
(= (nl $x) (progn (change-state! &sys-runs (+ 1 (get-state &sys-runs))) (+ $x 20)))
!(memoize plus)
!(memoize nl)
!(test (plus 5) 15)
!(test (plus 5) 15)
!(test (nl 5) 25)
!(test (nl 5) 25)
!(test (get-state &sys-runs) 2)

; Callers compiled before memoize! are rebuilt to call through the memo table:
!(bind! &mc-runs (new-state 0))
(= (mc $x) (progn (change-state! &mc-runs (+ 1 (get-state &mc-runs))) (+ $x 10)))
(= (mcaller $x) (+ (mc $x) (mc $x)))
!(memoize mc)
!(test (mcaller 5) 30)
!(test (get-state &mc-runs) 1)

; Even when memoize! precedes the callee's own clauses, an earlier caller in the
; same file is rebuilt to call through the memo table:
!(bind! &ml-runs (new-state 0))
(= (early-caller $x) (+ (late-mc $x) (late-mc $x)))
!(memoize late-mc)
(= (late-mc $x) (progn (change-state! &ml-runs (+ 1 (get-state &ml-runs))) (+ $x 20)))
!(test (early-caller 5) 50)
!(test (get-state &ml-runs) 1)

; Memoized recursion runs 11 times for 10 (not 177), and a second memoize!
; answers once without clearing existing cached entries (13 runs for 12, not 24):
!(bind! &cfib-runs (new-state 0))
(= (cfib $n)
   (progn (change-state! &cfib-runs (+ 1 (get-state &cfib-runs)))
          (if (< $n 2) $n (+ (cfib (- $n 1)) (cfib (- $n 2))))))
!(test (collapse (memoize cfib)) (True))
!(test (cfib 10) 55)
!(test (get-state &cfib-runs) 11)
!(test (collapse (memoize cfib)) (True))
!(test (cfib 12) 144)
!(test (get-state &cfib-runs) 13)
