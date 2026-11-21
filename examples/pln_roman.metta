!(import! &self ../lib/lib_pln)

(= (STV A) (stv 0.5 0.9))
(= (STV B) (stv 0.25 0.9))
(= (STV C) (stv 0.25 0.9))
(= (STV D) (stv 0.5 0.9))

(= (kb)
   ((Sentence ((Inheritance A B) (stv 0.25 0.9)) (1))
    (Sentence ((Inheritance A C) (stv 0.25 0.9)) (2))
    (Sentence ((Inheritance B D) (stv 0.5 0.9)) (3))
    (Sentence ((Inheritance C D) (stv 0.5 0.9)) (4))
   ))

!(test (PLN.Query (kb) (Inheritance A D))
       ((stv 0.5 0.9473684210526316) (1 2 3 4)))

;Induction from sentences 1 and 2, and abduction from 3 and 4: each premise's strength
;equals the prior of its target, so (Inheritance B C) gets the prior of C
!(test (collapse (|- ((Inheritance A B) (stv 0.25 0.9))
                     ((Inheritance A C) (stv 0.25 0.9))))
       (((Inheritance B C) (stv 0.25 0.4736842105263158))))
!(test (collapse (|- ((Inheritance B D) (stv 0.5 0.9))
                     ((Inheritance C D) (stv 0.5 0.9))))
       (((Inheritance B C) (stv 0.25 0.4736842105263158))))
