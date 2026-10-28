; Syntax reached through an unregistered head stays data until eval is asked.
!(test (let $head let (repr ($head slot 1 2))) "(let slot 1 2)")
!(test (let $head let* (repr ($head ((slot 1)) 2))) "(let* ((slot 1)) 2)")
!(test (let $head let (let $data ($head $x 1 2) (eval $data))) 2)
!(test (let $head let* (let $data ($head (($x 1)) 2) (eval $data))) 2)
!(test (let $head if ($head True yes no)) (quote (if True yes no)))
!(test (let $head quote ($head (a b))) (quote (quote (a b))))

; The handle is a created space even while empty. Fresh spaces stay distinct.
!(test (let $space (new-space) (get-metatype $space)) Grounded)
!(test (let $space (new-space) (collapse (get-atoms $space))) ())
!(test (let* (($first (new-space)) ($second (new-space)))
          (progn (add-atom $first (fact 1))
                 (collapse (match $second (fact $x) $x)))) ())
!(test (let* (($first (new-space)) ($second (new-space))) (== $first $second)) False)
!(test (get-metatype unrelated-symbol) Symbol)
!(test (get-metatype let) Grounded)
!(test (get-metatype let*) Grounded)

; The same syntax remains computational in authored patterns.
!(test (case 3 (((let $x 1 (+ $x 2)) matched-case) ($_ missed))) matched-case)
(= (computed-let-head (let $x 1 (+ $x 2))) matched-head)
!(test (collapse (computed-let-head 3)) (matched-head))
