; A removed definition takes its metadata with it: specialization, inferred
; types and determinism checks see only the definitions that remain.
(= (md-inc $x) (+ $x 1))

; Removing one arity's last equation leaves the other arity's alone:
(= (mho $f 1) ($f 10))
(= (mho $f 1 2) ($f 20))
!(test (remove-atom &self (= (mho $f 1) $b)) True)
!(test (collapse (mho md-inc 1)) ())
!(test (collapse (mho md-inc 1 2)) (21))

; Removing one of an arity's two equations by a pattern:
(= (sv $f 1) ($f 10))
(= (sv $f 2) ($f 20))
!(test (collapse (sv md-inc 1)) (11))
!(test (remove-atom &self (= (sv $f 1) $b)) True)
!(test (collapse (sv md-inc 1)) ())
!(test (collapse (sv md-inc 2)) (21))

; Two equal equations removed together leave nothing behind for a later load:
(= (ho_dup $f 1) ($f 10))
(= (ho_dup $f 1) ($f 10))
!(test (remove-atom &self (= (ho_dup $f 1) ($f 10))) True)
!(import! &self imports/removal_ho_dup)
!(test (collapse (ho_dup md-inc 1)) ())
!(test (collapse (ho_dup md-inc 2)) (21))

; A removed definition's inferred type does not constrain a new one:
(= (inf_ghost $x) (+ $x 1))
!(test (remove-atom &self (= (inf_ghost $x) (+ $x 1))) True)
!(import! &self imports/removal_inf_ghost)
(= (use_inf) (inf_ghost "hello"))
!(test (let $r (use_inf) compiled) compiled)

; A removed equation is no overlap for a deterministic function's next one:
(: det_zombie (-[semidet]-> Number Number))
(= (det_zombie 1) 10)
!(test (remove-atom &self (= (det_zombie $x) $b)) True)
!(add-atom &self (= (det_zombie 1) 99))
!(test (det_zombie 1) 99)
