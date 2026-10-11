; Store the same equation under two independent owners.
!(bind! &foo (new-space))
!(add-atom &self (= (f) 1))
!(add-atom &foo (= (f) 1))

; Default evaluation uses &self; eval/2 selects &foo explicitly.
!(test (collapse (f)) (1))
!(test (eval (f) &foo) 1)

; Removing &foo's copy leaves &self's data and executable behavior intact.
!(remove-atom &foo (= (f) 1))
!(test (match &self (= (f) $result) $result) 1)
!(test (collapse (f)) (1))

; A space's program calls its own functions and builtins, also through a
; function value, and never &self's functions.
(= (h) self-h)
!(add-atom &bar (= (g) 2))
!(add-atom &bar (= (calls-g) (g)))
!(add-atom &bar (= (inc $x) (+ $x 1)))
!(add-atom &bar (= (app $fn $x) ($fn $x)))
!(add-atom &bar (= (calls-h) (h)))
!(test (eval (calls-g) &bar) 2)
!(test (eval (app inc 4) &bar) 5)
!(test (car-atom (eval (calls-h) &bar)) h)
!(test (car-atom (collapse (calls-g))) (calls-g))

; Importing into a space compiles the source into that space's program.
!(import! &baz imports/overhaul/space_function_payload)
!(test (eval (payload-fn 2) &baz) 20)
!(test (collapse (match &baz (payload-marker) yes)) (yes))
!(test (car-atom (collapse (payload-fn 2))) (payload-fn 2))
!(import! &self imports/overhaul/space_function_payload)
!(test (payload-fn 3) 30)
