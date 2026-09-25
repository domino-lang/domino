; StuckArg: the two draws are paired only when the argument is positive, so
; whether they are paired is a question for the solver, not the text.
(define-fun randomness-mapping-StuckArg
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (and
        (= sample-id-left  (sample-id "p" "StuckArg" "s"))
        (= sample-id-right (sample-id "p" "StuckArg" "s"))
        (= sample-offset-left 0)
        (= sample-offset-right 0)
        (> <arg-GL-StuckArg-x> 0))
)
