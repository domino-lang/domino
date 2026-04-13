(define-lemma <relation-case-i-lt-dminusone-CoreIdeal-LastHybrid-GBLG>
    (
        (old-state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
        (return-left <OracleReturn_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredSimProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>) 1))
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-dminusone-CoreIdeal-LastHybrid-GBLG>
    (
        (old-state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
        (return-left <OracleReturn_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredSimProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (- (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>) 1))
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-d-CoreIdeal-LastHybrid-GBLG>
    (
        (old-state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
        (return-left <OracleReturn_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredSimProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>))
        (= return-left.value return-right.value)
    )
)