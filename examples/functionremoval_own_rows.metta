; Removing a function atom erases only the clauses of the rows it removed.
(= (k 1) 3)

; (= (k $x) $b) takes &other's data row (= $h 1), which has no clause, so k
; keeps its own:
!(add-atom &other (= $h 1))
!(test (remove-atom &other (= (k $x) $b)) True)
!(test (k 1) 3)

; So does a ground pattern that takes a data row with variables:
!(add-atom &other (= $h $v))
!(test (remove-atom &other (= (k 1) 3)) True)
!(test (k 1) 3)

; An equal definition added to another space brings its own clause, and
; removing it there leaves the first:
!(add-atom &other (= (k 1) 3))
!(test (remove-atom &other (= (k 1) 3)) True)
!(test (k 1) 3)
!(test (remove-atom &self (= (k 1) 3)) True)
!(test (collapse (match &self (= (k 1) $b) $b)) ())

; A ground pattern that takes a definition with variables takes its clause too:
(= (const $x) 42)
!(test (remove-atom &self (= (const 1) 42)) True)
!(test (== (const 99) 42) False)

; A file loaded into a second space is stored there without being compiled
; again, so removing it there leaves the first space's definition:
!(import! &self imports/removal_k)
!(import! &other imports/removal_k)
!(test (remove-atom &other (= (removal-k 1) 3)) True)
!(test (removal-k 1) 3)
