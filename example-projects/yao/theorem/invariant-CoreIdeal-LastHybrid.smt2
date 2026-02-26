(declare-const d Int)

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
            (> d 1)
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (> d 1)
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (= d 1)
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (= d 1)
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
        ; map Sim to LayeredSim for i < d
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_0"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_0"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_1"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_1"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_2"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_2"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_3"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_3"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        ; map Sim to Sim for i = d 
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_0"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_0"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_1"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_1"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_2"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_2"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_3"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
            (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_3"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        ; map Keys to LayeredKeys for i < d - 1
        (and 
            (< <arg-GBLG-i> (- d 1))
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (< <arg-GBLG-i> (- d 1))
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        ; map Keys to TopKeys for i = d - 1
        (and 
            (= <arg-GBLG-i> (- d 1))
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> (- d 1))
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        ; map Keys to BotKeys for i = d
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "KeysBot" "GETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> d)
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "KeysBot" "GETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
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

(define-state-relation equal-z
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i d)
                (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i j)))
            )
            (=>
                (= i d)
                (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.z j))
            )
            (=>
                (= i (+ d 1))
                (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.z j))
            )
        )
    )
)

(define-state-relation equal-T
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i d)
                (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i j)))
            )
            (=>
                (= i d)
                (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.T j))
            )
            (=>
                (= i (+ d 1))
                (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.T j))
            )
        )
    )
)

(define-state-relation equal-flag
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i d)
                (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i j)))
            )
            (=>
                (= i d)
                (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.flag j))
            )
            (=>
                (= i (+ d 1))
                (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.flag j))
            )
        )
    )
)

(define-state-relation invariant
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    (and 
        (equal-z state-left state-right)
        (equal-T state-left state-right)
        (equal-flag state-left state-right)
    )
)

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
        (< i (- d 1))
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
        (= i (- d 1))
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
        (= i d)
        (= return-left.value return-right.value)
    )
)

(assert 
    (=
        (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>)
        d
    )
)