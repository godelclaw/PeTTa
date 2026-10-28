; Predeclaring a name is not installing its equation.
(= (forward-caller) (forward-target 5))
!(test (forward-caller) (quote (forward-target 5)))
(= (forward-target $x) (+ $x 1))
!(test (forward-caller) 6)

; Syntax through a variable is data before, and a genuine function after,
; the user's equation is installed. Authored let syntax still binds.
!(test (let $head let ($head slot 1 2)) (quote (let slot 1 2)))
(= (let $a $b $c) (custom-let $a $b $c))
!(test (let $head let ($head slot 1 2)) (custom-let slot 1 2))
!(test (let $x 1 (+ $x 2)) 3)

; Eta expansion replaces the provisional source arity by a callable arity.
(= (eta-pair $x $y) (pair $x $y))
(= (eta-forward $x) (eta-pair $x))
!(test ((eta-forward 1) 2) (pair 1 2))
!(test (let $p (eta-forward 1) ($p 2)) (pair 1 2))
!(test (let $f eta-forward (($f 1) 2)) (pair 1 2))
