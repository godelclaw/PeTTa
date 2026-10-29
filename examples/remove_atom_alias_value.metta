; Store selection uses the raw declaration; an alias's expansion is its value
; type, even when that expansion looks like a function or kind declaration.
(: ArrowValueAlias (Alias (-> Number Number)))
(: arrow-value ArrowValueAlias)
!(test (remove-atom &self (: arrow-value ArrowValueAlias)) True)
; Compilation must no longer see the removed arrow-valued symbol declaration.
!(test (add-atom &self (= (arrow-probe) (+ arrow-value 1))) True)

!(add-atom &self (: KindValueAlias (Alias (Foreign 1))))
!(add-atom &self (: kind-value KindValueAlias))
!(test (let $removed (remove-atom &self ($op kind-value KindValueAlias))
          ($removed (is-var $op))) (True True))
!(test (add-atom &self (= (kind-probe) (+ kind-value 1))) True)

; A function declaration and an alias-valued symbol declaration can share a
; name. Removing the value declaration must leave the function store alone.
!(add-atom &self (: shared-value (-> Number Number)))
!(add-atom &self (: shared-value ArrowValueAlias))
!(test (remove-atom &self (: shared-value ArrowValueAlias)) True)
!(test (let (Error $e $kind)
          (catch (add-atom &self (= (shared-value "bad") "bad"))) $kind) typecheck)
!(test (remove-atom &self (: shared-value (-> Number Number))) True)
!(test (add-atom &self (= (shared-value "hi") "ok")) True)
!(test (shared-value "hi") "ok")

; A batch keeps the store tags and normalized payloads after its aliases go.
!(add-atom &self (: BatchArrowValue (Alias (-> Number Number))))
!(add-atom &self (: batch-value BatchArrowValue))
!(add-atom &self (: batch-function (-> Number Number)))
!(test (let $removed (remove-atom &self (: $name $type))
          ($removed (is-var $name) (is-var $type))) (True True True))
!(test (add-atom &self (= (batch-probe) (+ batch-value 1))) True)
!(test (add-atom &self (= (batch-function "hi") "ok")) True)
!(test (batch-function "hi") "ok")
