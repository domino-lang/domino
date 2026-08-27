(define-lemma <case-i-lt-dminusone-GBLG>
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

(define-lemma <case-i-is-dminusone-GBLG>
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

(define-lemma <case-i-is-d-GBLG>
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
