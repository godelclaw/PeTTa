; Completed calls check their result type; partial applications keep their
; supplied arguments and check the remaining arguments when completed.
(: corrected-add (-> Number Number Number))
(= (corrected-add $x $y) (+ $x $y))
!(test ((corrected-add 40) 2) 42)
!(test (let $p (corrected-add 40) ($p 2)) 42)
!(test (let $f corrected-add (let $p ($f 40) ($p 2))) 42)
!(test (let $f corrected-add (($f 40) 2)) 42)
!(test (collapse (corrected-add "wrong")) ())
(: corrected-text (-> Number String String))
(= (corrected-text $number $text) $text)
!(test ((corrected-text 1) "ok") "ok")
!(test (let $p (corrected-text 1) ($p "ok")) "ok")
(: corrected-bad-result (-> Number Number Number))
(= (corrected-bad-result $x $y) "wrong")
!(test (collapse ((corrected-bad-result 1) 2)) ())

; A match template is an answer only in the branch that executes it.
(= (corrected-space) &corrected-template)
!(add-atom (corrected-space) (fact 3))
(= (corrected-template $flag $template)
   (if $flag (match (corrected-space) (fact $x) $template) nope))
!(test (corrected-template False ignored) nope)
!(test (corrected-template True ignored) ignored)
!(test (match (corrected-space) (fact $x) (+ $x 1)) 4)

; Empty spaces are values before they have any facts, and remain distinct.
!(test (let $s (new-space) (is-space $s)) True)
!(test (let $s (new-space) (collapse (match $s $x $x))) ())
!(test (let* (($a (new-space)) ($b (new-space))
              ($write (add-atom $a (value 7))))
             ((collapse (match $a (value $x) $x))
              (collapse (match $b (value $x) $x)))) ((7) ()))
!(import! &self ../lib/lib_he)
!(test (let $s (new-space)
             (let $write (add-atom $s (value 9))
                  (collapse (match $s (value $x) $x)))) (9))

; Python text remains text; Boolean values retain their Boolean meaning.
!(test (py-call (str "true")) "true")
!(test (== (py-call (str "abc")) abc) False)
!(test (py-call (bool 1)) True)
!(test (py-call (str "")) "")
!(test (py-call (list "ab")) ("a" "b"))
