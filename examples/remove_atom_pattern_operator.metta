; Choosing how to add or remove an atom binds nothing in it.

; ($op (foo 1) 2) takes a row it unifies with, data or a definition, and leaves
; $op unbound:
!(add-atom &d1 (rel (foo 1) 2))
!(test (let $r (remove-atom &d1 ($op (foo 1) 2)) ($r (is-var $op))) (True True))
!(test (collapse (get-atoms &d1)) ())
(= (opdef 1) 2)
!(test (remove-atom &self ($op (opdef 1) 2)) True)
!(test (== (opdef 1) 2) False)

; An atom with an unbound operator is added as data, not as a definition:
!(add-atom &d2 ($op2 (bar 1) 2))
!(test (collapse (match &d2 ($o (bar 1) 2) (is-var $o))) (True))
!(test (== (bar 1) 2) False)

; A pattern that could take a definition of any function is refused:
!(test (let (Error instantiation_error $c) (catch (remove-atom &self ($op $h $b))) raised) raised)
