(define-lemma <relation-case-i-is-one-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 1)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-two-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-gt-two-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i 2)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-abort-case-i-is-one-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 1)
        (= ((_ is mk-abort) return-left.value)
           ((_ is mk-abort) return-right.value))
    )
)

(define-lemma <relation-abort-case-i-is-two-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
          (= ((_ is mk-abort) return-left.value)
              ((_ is mk-abort) return-right.value))
    )
)

(define-lemma <relation-abort-case-i-is-two-assumptions-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
        (and
            (= (select old-state-left.Keys.flag (mk-tuple2 2 l)) (select old-state-right.KeysBot.flag l))
            (= (select old-state-left.Keys.z (mk-tuple2 2 l)) (select old-state-right.KeysBot.z l))
            (= (select old-state-left.Keys.T (mk-tuple2 2 l)) (select old-state-right.KeysBot.T l))

            (= (select old-state-left.Keys.flag (mk-tuple2 2 r)) (select old-state-right.KeysBot.flag r))
            (= (select old-state-left.Keys.z (mk-tuple2 2 r)) (select old-state-right.KeysBot.z r))
            (= (select old-state-left.Keys.T (mk-tuple2 2 r)) (select old-state-right.KeysBot.T r))

            (= (select old-state-left.Keys.flag (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.flag (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.z (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.z (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.T (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.T (mk-tuple2 3 j)))
        )
    )
)

(define-lemma <relation-abort-case-i-gt-two-CoreReal-FirstHybrid-GBLG>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayeredGateProxy_<$<!d!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i 2)
          (= ((_ is mk-abort) return-left.value)
              ((_ is mk-abort) return-right.value))
    )
)