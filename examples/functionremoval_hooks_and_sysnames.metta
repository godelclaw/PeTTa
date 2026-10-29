; Function-change hooks run every registered listener once, without duplicating
; add-atom or remove-atom answers, and last-clause removal skips static Prolog
; built-ins of the same name.
!(import! &self (library lib_memo))

(= (st 1) a)
!(memoize st)
!(test (collapse (st 1)) (a))
!(test (collapse (add-atom &self (= (st 1) b))) (True))
!(test (collapse (st 1)) (a b))
!(test (collapse (remove-atom &self (= (st 1) a))) (True))
!(test (collapse (st 1)) (b))
!(test (is-memoized st) true)
!(test (collapse (remove-atom &self (= (st 1) b))) (True))
!(test (is-memoized st) false)
!(test (collapse (add-atom &self (= (plain-hook 1) c))) (True))

; Removing a function named like a static Prolog built-in skips static arities:
(= (plus $x) (+ $x 1))
(= (nl $x) (+ $x 2))
!(test (plus 1) 2)
!(test (nl 1) 3)
!(test (remove-atom &self (= (plus $x) (+ $x 1))) True)
!(test (remove-atom &self (= (nl $x) (+ $x 2))) True)
!(test (collapse (plus 1)) ((plus 1)))
!(test (collapse (nl 1)) ((nl 1)))
