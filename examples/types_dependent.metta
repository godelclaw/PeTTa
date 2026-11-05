;get-type extension for numbers:
(= (get-type $x)
   (catch (if (== (% $x 2) 0)
              EvenNumber)))

; Derived reflection is queried explicitly by the application. Runtime
; contracts use intrinsic types and do not execute get-type extensions.
(: f (-> Number Number Number))
(= (f $x $y)
   (let EvenNumber (get-type $x)
     (let EvenNumber (get-type $y) (+ $x $y))))

!(test (f 2 4) 6)

;get-type extension for list of even numbers:
(= (get-type (cons $head $tail))
   (if (== (get-type $head) EvenNumber)
       (if (== $tail ())
           EvenNumberList
           (get-type $tail))))

;try it:
(: g (-> Atom Bool))
(= (g $L)
   (let EvenNumberList (get-type $L) True))

!(test (g (2 4 6)) True)
