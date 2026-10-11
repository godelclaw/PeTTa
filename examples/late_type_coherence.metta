; A caller sees a type declaration even when the declaration appears later.
(= (typed-through $x) (typed-identity $x))
(: typed-identity (-> Number Number))
(= (typed-identity $x) $x)

!(test (collapse (typed-through 7)) (7))
!(test (car-atom (catch (typed-through (car-atom ("bad" 1))))) Error)

; Adding and removing a type updates callers that are already compiled.
(= (dynamic-identity $x) $x)
(= (dynamic-through $x) (dynamic-identity $x))

!(test (collapse (dynamic-through (car-atom ("before" 1)))) ("before"))
!(add-atom &self (: dynamic-identity (-> Number Number)))
!(test (car-atom (catch (dynamic-through (car-atom ("after-add" 1))))) Error)
!(test (collapse (dynamic-through 7)) (7))
!(remove-atom &self (: dynamic-identity (-> Number Number)))
!(test (collapse (dynamic-through (car-atom ("after-remove" 1)))) ("after-remove"))
