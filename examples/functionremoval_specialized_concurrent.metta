; Threads removing different equations of a specialized function each answer:
; the specializations they forget are forgotten one thread at a time.
(= (inc $x) (+ $x 1))
(= (twice $f) ($f 1))
(= (twice $f) ($f 2))
!(test (collapse (twice inc)) (2 3))
(= (dropeq $i) (if (remove-atom &self (= (twice $f) ($f $i))) (add-atom &swon $i) (add-atom &slost $i)))
!(hyperpose ((dropeq 1) (dropeq 2) (dropeq 1) (dropeq 2) (dropeq 1) (dropeq 2) (dropeq 1) (dropeq 2)))
!(test (size-atom (collapse (match &swon $w $w))) 2)
!(test (size-atom (collapse (match &slost $l $l))) 6)
!(test (collapse (match &self (= (twice $f) $b) $b)) ())
