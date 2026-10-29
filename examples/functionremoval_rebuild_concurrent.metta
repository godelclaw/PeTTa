; Threads calling a function while another thread removes and adds back a
; definition it mentions always find its clauses: a rebuilt function swaps
; them in one step.
(= (twice $f) ($f 1))
(= (probe) (collapse (match &empty_dummy (= (twice $f) ($f 1)) ok)))
(= (reader $n) (if (== $n 0) done (let $_ (probe) (reader (- $n 1)))))
(= (toggler $n)
   (if (== $n 0) done
       (let $_ (remove-atom &self (= (twice $f) ($f 1)))
         (let $_ (add-atom &self (= (twice $f) ($f 1)))
           (toggler (- $n 1))))))
!(test (collapse (hyperpose ((toggler 100) (reader 20000) (reader 20000) (reader 20000) (reader 20000))))
       (done done done done done))
