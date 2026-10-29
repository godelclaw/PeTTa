; Re-imported source forms share code, but each imported row supports it.
!(import! &self imports/shared_support)
!(import! &copy imports/shared_support)
!(test (collapse (support-dup)) (a b a))
!(test (remove-atom &self (= (support-k 1) 3)) True)
!(test (support-k 1) 3)
!(test (size-atom (collapse (match &copy (= (support-k 1) 3) 1))) 1)
!(test (remove-atom &copy (= (support-k 1) 3)) True)
!(test (== (support-k 1) 3) False)

; A later import restores missing code without duplicating surviving forms.
!(import! &third imports/shared_support)
!(test (support-k 1) 3)
!(test (collapse (support-dup)) (a b a))

; Dynamic additions remain independent clauses, even with an equal body.
!(test (add-atom &dynamic (= (support-k 1) 3)) True)
!(test (collapse (support-k 1)) (3 3))
!(test (remove-atom &third (= (support-k 1) 3)) True)
!(test (collapse (support-k 1)) (3))
!(test (remove-atom &dynamic (= (support-k 1) 3)) True)
!(test (== (support-k 1) 3) False)
