; Cached declarations follow actual removed rows, not the unbound query fields.
(: removed-op (-> Number Number))
!(test (let $removed (remove-atom &self ($op removed-op (-> Number Number)))
          ($removed (is-var $op))) (True True))
!(test (collapse (match &self (: removed-op $t) $t)) ())
!(test (add-atom &self (= (removed-op "hi") "ok")) True)
!(test (removed-op "hi") "ok")

(: removed-type (-> Number Number))
!(test (let $removed (remove-atom &self (: removed-type $type))
          ($removed (is-var $type))) (True True))
!(test (add-atom &self (= (removed-type "hi") "ok")) True)
!(test (removed-type "hi") "ok")

(: removed-poly (-> $t $t))
!(test (remove-atom &self (: removed-poly $type)) True)
!(test (add-atom &self (= (removed-poly $x) "constant")) True)
!(test (removed-poly 1) "constant")

; Removing aliases and their users together snapshots their old normalized types.
!(add-atom &self (: RemovedAlias (Alias Number)))
!(add-atom &self (: RemovedAlias2 (Alias RemovedAlias)))
!(add-atom &self (: alias-user (-> RemovedAlias2 RemovedAlias2)))
!(test (let $removed (remove-atom &self (: $name $type))
          ($removed (is-var $name) (is-var $type))) (True True True))
!(test (add-atom &self (= (alias-user "hi") "ok")) True)
!(test (alias-user "hi") "ok")
!(test (remove-atom &self (: $name $type)) False)
; Both alias stores were removed too, so the dependent alias may be redeclared.
!(test (add-atom &self (: RemovedAlias2 (Alias String))) True)
!(add-atom &self (: alias-reuse (-> RemovedAlias2 RemovedAlias2)))
!(test (add-atom &self (= (alias-reuse "hi") "ok")) True)
!(test (alias-reuse "hi") "ok")
