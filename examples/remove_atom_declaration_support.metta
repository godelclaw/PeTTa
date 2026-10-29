; Equal declarations share a cache entry; one remaining row keeps it alive.
(: support-fn (-> Number Number))
(: support-fn (-> Number Number))
!(test (remove-atom &self (: support-fn (-> Number Number))) True)
!(test (let (Error $e $kind) (catch (add-atom &self (= (support-fn "hi") "bad"))) $kind) typecheck)
!(test (remove-atom &self (: support-fn (-> Number Number))) True)
!(test (add-atom &self (= (support-fn "hi") "ok")) True)
!(test (support-fn "hi") "ok")

(: support-value String)
(: support-value String)
!(test (remove-atom &self (: support-value String)) True)
!(test (let (Error $e $kind) (catch (add-atom &self (= (support-vprobe) (+ support-value 1)))) $kind) typecheck)
!(test (remove-atom &self (: support-value String)) True)
!(test (add-atom &self (= (support-vprobe) (+ support-value 1))) True)

; Canonically equivalent function schemes support the same cache record.
!(add-atom &self (: SupportNum (Alias Number)))
!(add-atom &self (: support-equivalent (-> Number Number)))
!(add-atom &self (: support-equivalent (-> SupportNum SupportNum)))
!(test (remove-atom &self (: support-equivalent (-> Number Number))) True)
!(test (let (Error $e $kind) (catch (add-atom &self (= (support-equivalent "hi") "bad"))) $kind) typecheck)
!(test (remove-atom &self (: support-equivalent (-> SupportNum SupportNum))) True)
!(test (add-atom &self (= (support-equivalent "hi") "ok")) True)

; Wildcard data is not a source declaration and cannot keep a signature alive.
!(add-atom &self (: support-data (-> Number Number)))
!(add-atom &self ($tag support-data (-> Number Number)))
!(test (remove-atom &self (: support-data (-> Number Number))) True)
!(test (add-atom &self (= (support-data "hi") "ok")) True)

; Kind stores retain their schema until the last matching declaration goes.
!(add-atom &self (: &support-jobs (SpaceOf (job Number))))
!(add-atom &self (: &support-jobs (SpaceOf (job Number))))
(= (support-put $s $v) (add-atom $s (job $v)))
!(test (remove-atom &self (: &support-jobs (SpaceOf (job Number)))) True)
!(test (let (Error $e $kind) (catch (support-put &support-jobs "bad")) $kind) typecheck)
!(test (remove-atom &self (: &support-jobs (SpaceOf (job Number)))) True)
!(test (support-put &support-jobs "ok") True)
