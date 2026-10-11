; A superpose of an empty list yields no results, alone or among other branches.
!(test (collapse (superpose ())) ())
!(test (collapse (superpose ((superpose ()) 7 7))) (7 7))
!(test (collapse (superpose ((superpose ()) (superpose ())))) ())
(= (nothing) (superpose ()))
!(test (collapse (nothing)) ())

; One branch is still built once.
!(test (collapse (superpose (5))) (5))
