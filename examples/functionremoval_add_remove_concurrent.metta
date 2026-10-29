; Threads adding and removing one definition at once leave no clause behind
; once its rows are gone: a row and the clause it owns appear together.
(= (adds $n) (if (== $n 0) () (let $_ (add-atom &self (= (churn) 1)) (adds (- $n 1)))))
(= (dels $n) (if (== $n 0) () (let $_ (remove-atom &self (= (churn) 1)) (dels (- $n 1)))))
(= (drain) (if (remove-atom &self (= (churn) 1)) (drain) done))
!(hyperpose ((adds 300) (dels 300) (adds 300) (dels 300)))
!(test (drain) done)
!(test (collapse (match &self (= (churn) $v) $v)) ())
!(test (== (collapse (churn)) ((churn))) True)
