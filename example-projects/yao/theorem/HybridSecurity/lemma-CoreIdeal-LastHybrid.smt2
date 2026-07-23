(define-lemma <relation-case-i-lt-dminusone-CoreIdeal-LastHybrid-GBLG>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- (<theorem-consts-HybridSecurity-d> <<theorem-consts>>) 1))
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-dminusone-CoreIdeal-LastHybrid-GBLG>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (- (<theorem-consts-HybridSecurity-d> <<theorem-consts>>) 1))
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-d-CoreIdeal-LastHybrid-GBLG>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
        (= return-left.value return-right.value)
    )
)
