!(import! &self (library lib_memo))

; A cached parent also depends on callees that are not themselves memoized.
(= (memo-dep-child $x) (+ $x 1))
(= (memo-dep-middle $x) (memo-dep-child $x))
(= (memo-dep-parent $x) (memo-dep-middle $x))
!(memoize memo-dep-parent)
!(test (collapse (memo-dep-parent 5)) (6))
!(add-atom &self (= (memo-dep-child $x) (+ $x 2)))
!(test (collapse (memo-dep-parent 5)) (6 7))
!(remove-atom &self (= (memo-dep-child $x) (+ $x 1)))
!(test (collapse (memo-dep-parent 5)) (7))
!(remove-atom &self (= (memo-dep-child $x) (+ $x 2)))
!(test (collapse (memo-dep-parent 5)) (quote ((memo-dep-child 5))))
!(add-atom &self (= (memo-dep-child $x) (+ $x 3)))
!(test (collapse (memo-dep-parent 5)) (8))

; Defining an absent dynamic head invalidates the previously cached data.
(= (memo-dep-dispatch $f $x) ($f $x))
!(memoize memo-dep-dispatch)
!(test (memo-dep-dispatch memo-dep-new 5) (quote (memo-dep-new 5)))
!(add-atom &self (= (memo-dep-new $x) (+ $x 10)))
!(test (memo-dep-dispatch memo-dep-new 5) 15)
!(remove-atom &self (= (memo-dep-new $x) (+ $x 10)))
!(test (memo-dep-dispatch memo-dep-new 5) (quote (memo-dep-new 5)))
!(add-atom &self (= (memo-dep-new $x) (+ $x 20)))
!(test (memo-dep-dispatch memo-dep-new 5) 25)

; The ready-value path observes the same dependency without reevaluating data.
(= (memo-dep-reduce $f $x) (reduce ($f $x)))
!(memoize memo-dep-reduce)
!(test (memo-dep-reduce memo-dep-ready 4) (quote (memo-dep-ready 4)))
!(add-atom &self (= (memo-dep-ready $x) (+ $x 30)))
!(test (memo-dep-reduce memo-dep-ready 4) 34)
