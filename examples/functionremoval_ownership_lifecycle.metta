; A row keeps owning its clause when the clause is recompiled or restored.

; Adding a callee recompiles its caller; removing the caller erases the
; recompiled clause:
(= (lc-callee) 1)
(= (lc-caller) (lc-callee))
!(add-atom &self (= (lc-callee) 2))
!(test (collapse (lc-caller)) (1 2))
!(test (remove-atom &self (= (lc-caller) (lc-callee))) True)
!(test (== (collapse (lc-caller)) (1 2)) False)

; A rejected addition restores the definitions it touched, and they stay
; removable:
(: lc-typed (-> Number Number))
(= (lc-typed 1) 2)
!(test (let (Error $e $c) (catch (add-atom &self (= (lc-typed "x") 3))) rejected) rejected)
!(test (lc-typed 1) 2)
!(test (remove-atom &self (= (lc-typed 1) 2)) True)
!(test (== (lc-typed 1) 2) False)
