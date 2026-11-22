; Applications are decided in the program state in which they are reached.

; Line-break and let invariance: adding an equation and calling it in the same body.
(= (remember $k $v)
   (let $u (add-atom &self (= (recall $k) $v))
     (recall $k)))
!(test (remember color blue) blue)
!(test (recall color) blue)

; A computed equation value is called later in the same body.
(= (install-and-call $eq)
   (let $u (add-atom &self $eq)
     (late-rule 3)))
!(test (install-and-call (quote (= (late-rule $x) (* $x 10)))) 30)

; Earlier definitions refresh when a symbol they compiled as data becomes a function.
(= (use-before-def $x) (defined-later $x))
!(test (use-before-def 4) (defined-later 4))
!(add-atom &self (= (defined-later $x) (+ $x 1)))
!(test (use-before-def 4) 5)

; Atom-held arguments stay held and exceptions still reach catch after an edit.
(: hold-late (-> Atom %Undefined%))
(= (install-hold)
   (let $u (add-atom &self (= (hold-late $x) (held $x)))
     (hold-late (+ 1 2))))
!(test (install-hold) (quote (held (+ 1 2))))

; Arguments evaluated after an editing argument or value-headed call see the edit.
(= (add-arg-fn) (add-atom &self (= (arg-target) ok)))
(= (call-through $f) (Pair ($f) (arg-target)))
!(test (call-through add-arg-fn) (Pair True ok))

; Relational inversion keeps demand even inside a body that edits.
(= (pplus Z $y) $y)
(= (pplus (S $x) $y) (S (pplus $x $y)))
(= (invert-after-edit $eq)
   (let $u (add-atom &self $eq)
     (collapse (let (pplus $a $b) (S (S Z)) (Pair $a $b)))))
!(test (invert-after-edit (quote (= (noted) 1)))
       ((Pair Z (S (S Z))) (Pair (S Z) (S Z)) (Pair (S (S Z)) Z)))

; Later alternatives and match answers after an edit see it; consumer-resumed
; alternatives stay frozen equally for multi-clause functions and superpose.
(= (choice-edit) (let $u (add-atom &self (= (choice-later) seen)) first))
(= (choice-edit) (choice-later))
!(test (collapse (choice-edit)) (first seen))

(= (gen-frozen) (gf-one))
(= (gen-frozen) (gf-two))
!(test (collapse (let $x (gen-frozen) (let $u (add-atom &self (= (gf-two) 2)) $x)))
       (quote ((gf-one) (gf-two))))
!(test (collapse (let $x (superpose ((gf-one) (gf-two-b))) (let $u (add-atom &self (= (gf-two-b) 2)) $x)))
       (quote ((gf-one) (gf-two-b))))
