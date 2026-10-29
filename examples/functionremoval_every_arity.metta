; When a function's last clause goes, callers of every arity see data syntax,
; not only callers of the arity removed last.
(= (ea-f 1) 10)
(= (ea-f 1 2) 20)
(= (ea-c1 $x) (ea-f $x))
(= (ea-c2 $x $y) (ea-f $x $y))
!(test (collapse (ea-c2 1 2)) (20))
!(test (remove-atom &self (= (ea-f 1 2) 20)) True)
!(test (collapse (ea-c2 1 2)) ())
!(test (collapse (ea-c1 1)) (10))
!(test (remove-atom &self (= (ea-f 1) 10)) True)
!(test (collapse (ea-c1 1)) ((ea-f 1)))
!(test (collapse (ea-c2 1 2)) ((ea-f 1 2)))
