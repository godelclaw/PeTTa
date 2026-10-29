; Threads removing the same function atom each get an answer, and exactly one
; is told True: each erases only the clauses whose record it took.
(= (h 1) 2)
(= (claim $i) (if (remove-atom &self (= (h 1) 2)) (add-atom &won $i) (add-atom &lost $i)))
!(hyperpose ((claim 1) (claim 2) (claim 3) (claim 4) (claim 5) (claim 6) (claim 7) (claim 8)))
!(test (size-atom (collapse (match &won $w $w))) 1)
!(test (size-atom (collapse (match &lost $l $l))) 7)
!(test (collapse (match &self (= (h 1) $b) $b)) ())

; Threads removing equal definitions from two spaces each erase their own
; clause, and both answer True:
(= (k 1) 3)
!(add-atom &other (= (k 1) 3))
(= (claimk $space $i) (if (remove-atom $space (= (k 1) 3)) (add-atom &kwon $i) (add-atom &klost $i)))
!(hyperpose ((claimk &self 1) (claimk &other 2) (claimk &self 3) (claimk &other 4)
             (claimk &self 5) (claimk &other 6) (claimk &self 7) (claimk &other 8)))
!(test (size-atom (collapse (match &kwon $w $w))) 2)
!(test (size-atom (collapse (match &klost $l $l))) 6)
