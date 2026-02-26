(define-fun randomness-mapping-GETAOUT
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    (or 
        (and 
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
    )
)

(define-fun randomness-mapping-SETBIT
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    false
)

(define-fun randomness-mapping-GBLG
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    (or
        (and
            (= <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (= <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (= <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCN" "r"))
            (= sample-id-right (sample-id "Enc" "ENCN" "r"))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
        )
        (and
            (= <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCM" "r"))
            (= sample-id-right (sample-id "Enc" "ENCM" "r"))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
        )
        (and
            (> <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (> <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (> <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCN" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCN" "r"))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
        )
        (and
            (> <arg-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCM" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCM" "r"))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
        )
    )
)

(define-fun randomness-mapping-GETKEYSIN
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    false
)

(define-state-relation invariant
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (= i 1)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.flag j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.z j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.T j))
                )
            )
            (=>
                (= i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.flag j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.z j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.T j))
                )
            )
            (=>
                (> i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.RealLayersKeys.z (mk-tuple2 i j)))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.RealLayersKeys.T (mk-tuple2 i j)))
                )
            )
        )
    )
)

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