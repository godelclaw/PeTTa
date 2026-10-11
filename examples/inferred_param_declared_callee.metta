; A type declaration promises that the declared function's arguments are
; checked. Inference types an undeclared function's parameter from how its body
; uses it, and never demands that type of the function's callers (see
; inferred_sentinel_param.metta). So an inferred type proves nothing about a
; declared argument: wherever such a parameter reaches a declared function, the
; call keeps its check.
(: need-number (-> Number Number))
(= (need-number $x) $x)

; A wrapper passes its parameter straight through.
(= (wrap $x) (need-number $x))
!(test (wrap 7) 7)
!(test (car-atom (catch (wrap (car-atom ("bad" 1))))) Error)

; Each branch keeps its own check.
(= (either $c $x) (if $c (need-number $x) (box (need-number $x))))
!(test (either False 1) (box 1))
!(test (car-atom (catch (either True (car-atom ("bad" 1))))) Error)
!(test (car-atom (catch (either False (car-atom ("bad" 1))))) Error)

; A destructured parameter is a parameter too.
(= (first-of (pair $a $b)) (need-number $a))
!(test (first-of (pair 7 x)) 7)
!(test (car-atom (catch (first-of (pair (car-atom ("bad" 1)) x)))) Error)

; So are a parameter a lambda captures and a lambda's own parameter. Dynamic
; dispatch turns the error into no result.
(= (later $x) (let $f (|-> ($y) (need-number $x)) ($f 0)))
!(test (later 7) 7)
!(test (collapse (later (car-atom ("bad" 1)))) ())
(= (apply-later $v) (let $f (|-> ($y) (need-number $y)) ($f $v)))
!(test (apply-later 7) 7)
!(test (collapse (apply-later (car-atom ("bad" 1)))) ())

; An overloaded callee keeps its branch filters, so exactly one branch applies.
(: ov (-> Number Atom))
(: ov (-> String Atom))
(= (ov $x) (seen $x))
(= (wov $x) (ov $x))
!(test (wov 7) (seen 7))
!(test (wov "s") (seen "s"))
!(test (car-atom (catch (wov (car-atom ((sym) 1))))) Error)

; Inference still only adds knowledge: a sentinel never reaches the check.
(= (score $current $cand) (if (== $current none) $cand (need-number $current)))
!(test (score none 0.42) 0.42)
!(test (score 3 0.42) 3)
