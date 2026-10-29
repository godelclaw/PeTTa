; A removed row erases the very clause compiled from it.

; Equal definitions in two spaces keep their own clauses, in their own order:
(= (ident-pick) 1)
(= (ident-pick) 2)
!(add-atom &other (= (ident-pick) 1))
!(test (collapse (ident-pick)) (1 2 1))
!(test (remove-atom &other (= (ident-pick) 1)) True)
!(test (collapse (ident-pick)) (1 2))

; Compiling may alias a definition's variables, and its clause still goes:
(= (ident-choose $a $b)
   (if True
       (let red $a $a)
       (let blue $b $b)))
!(test (ident-choose red red) red)
!(test (remove-atom &self (= (ident-choose $a $b) $body)) True)
!(test (== (ident-choose red red) red) False)

; Equal text can compile differently once a declaration changes, and removing
; the copy in &other erases that copy's clause:
(: ident-helper (-> Number))
(= (ident-helper) 7)
(= (ident-f) (ident-helper))
!(remove-atom &self (: ident-helper (-> Number)))
!(remove-atom &self (= (ident-helper) 7))
!(add-atom &self (= (ident-helper) "ok"))
!(add-atom &other (= (ident-f) (ident-helper)))
!(test (collapse (ident-f)) ("ok"))
!(test (remove-atom &other (= (ident-f) (ident-helper))) True)
!(test (collapse (ident-f)) ())
