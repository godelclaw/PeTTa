; A change to a function's arrow declarations reaches the equations that were translated before it.
(: a A)
(: b B)

; A declaration added after its callers were translated,
(= (late $x) (seen $x))
(= (late-caller $x) (late $x))
(= (late-outer $x) (late-caller $x))
!(test (collapse (late-outer b)) ((seen b)))
!(add-atom &self (: late (-> A %Undefined%)))
!(test (car-atom (catch (late-outer (car-atom (b 1))))) Error)
!(test (collapse (late-outer a)) ((seen a)))
; and one that is removed, here by a pattern.
!(remove-atom &self (: late $type))
!(test (collapse (late-outer b)) ((seen b)))

; An argument declared Atom is passed unevaluated,
(= (quo $x) (quoted $x))
(= (quo-caller) (quo (+ 1 2)))
!(test (quo-caller) (quoted 3))
!(add-atom &self (: quo (-> Atom %Undefined%)))
!(test (quo-caller) (quote (quoted (+ 1 2))))
; and an Atom result holds the body.
(= (held $x) (+ $x 1))
!(test (held 6) 7)
!(add-atom &self (: held (-> Number Atom)))
!(test (held 6) (quote (+ 6 1)))
!(remove-atom &self (: held (-> Number Atom)))
!(test (held 6) 7)

; So do specializations of higher-order functions,
(= (apply-to $f $x) ($f $x))
(= (target $x) (reached $x))
(= (through $x) (apply-to target $x))
!(test (collapse (through b)) ((reached b)))
!(add-atom &self (: target (-> A %Undefined%)))
!(test (collapse (through (car-atom (b 1)))) ())
!(test (collapse (through a)) ((reached a)))
; and anonymous functions that were made earlier.
(= (inner $x) (kept $x))
!(bind! &made (new-space))
!(let $g (|-> ($x) (inner $x)) (add-atom &made (saved $g)))
!(test (collapse (match &made (saved $g) ($g b))) ((kept b)))
!(add-atom &self (: inner (-> A %Undefined%)))
!(test (collapse (match &made (saved $g) ($g b))) ())

; A declaration of another function leaves them as they were.
!(add-atom &self (: other (-> A %Undefined%)))
!(test (collapse (through a)) ((reached a)))

; A declaration that a stored equation cannot be translated with is refused, and nothing changes.
(= (taken $x) (took $x))
(= (taken-caller) (taken b))
!(test (car-atom (catch (add-atom &self (: taken (-> A %Undefined%))))) Error)
!(test (collapse (match &self (: taken $type) $type)) ())
!(test (taken-caller) (took b))
!(test (taken (car-atom (b 1))) (took b))

; An equation that is already running finishes as it was translated, and its next run follows the change.
(= (grow) (let $u (add-atom &self (= (grow) new)) old))
!(test (collapse (grow)) (old))
!(test (collapse (grow)) (old new))
(= (now $x) (was $x))
(= (running) (let $u (add-atom &self (: now (-> Atom %Undefined%))) (now (+ 1 2))))
!(test (running) (was 3))
!(test (running) (quote (was (+ 1 2))))
