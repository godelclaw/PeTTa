; An anonymous function never takes the name of a function the program defines.
(= (lambda_1 $x) (* $x 100))
(= (lambda_2 $x $y) (+ $x $y))

!(test (collapse (lambda_1 2)) (200))
!(test (collapse (let $f (|-> ($x) (+ $x 1)) ($f 2))) (3))
!(test (collapse (lambda_1 2)) (200))
!(test (collapse (let $g (|-> ($a $b) (* $a $b)) ($g 3 4))) (12))
!(test (collapse (lambda_2 3 4)) (7))
!(test (collapse (let $n 5 (let $h (|-> ($x) (+ $x $n)) ($h 1)))) (6))
