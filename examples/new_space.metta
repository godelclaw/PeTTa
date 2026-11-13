; Fresh spaces are first-class values, including while they are empty.
!(test (let $space (new-space) (is-space $space)) True)
!(test (let $space (new-space) (get-metatype $space)) Grounded)
!(test (let $space (new-space) (collapse (get-atoms $space))) ())
!(test (let $space (new-space) (collapse (match $space $x $x))) ())

; Two calls return distinct spaces and writes remain isolated.
!(test (let* (($first (new-space)) ($second (new-space)))
         (== $first $second)) False)
!(test (let* (($first (new-space)) ($second (new-space))
              ($_ (add-atom $first (value 7))))
         ((collapse (match $first (value $x) $x))
          (collapse (match $second (value $x) $x)))) ((7) ()))

; A pre-existing predicate name is never selected for a new space.
!(add-atom &space_1 (occupied))
!(test (let $space (new-space) (== $space &space_1)) False)
!(test (let $space (new-space) (collapse (match $space $x $x))) ())

; new-space has the same meaning in an equation body as at the call site.
(= (make-space) (new-space))
!(test (let $space (make-space)
         (let $_ (add-atom $space (inside))
           (collapse (match $space $x $x)))) ((inside)))
!(test (let* (($first (make-space)) ($second (make-space)))
         (== $first $second)) False)
