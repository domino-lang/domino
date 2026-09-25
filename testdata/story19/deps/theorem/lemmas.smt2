; `positive` is a dependency that only the solver can see is false: on the path of `Branch`
; where `x <= 0` it is unsatisfiable, and no terminal says so.
(define-lemma <relation-positive-gl-gr-Branch>
    (old-state-left old-state-right return-left return-right (x Int))
    (> x 0))

(define-lemma <relation-needs-positive-gl-gr-Branch>
    (old-state-left old-state-right return-left return-right (x Int))
    (= return-left.value return-right.value))

(define-lemma <relation-skipped-gl-gr-Admitted>
    (old-state-left old-state-right return-left return-right (x Int))
    false)
