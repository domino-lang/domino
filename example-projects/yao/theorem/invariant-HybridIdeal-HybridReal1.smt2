(declare-const h Int)
(declare-const d Int)
(declare-const hplusone Int)

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
            (= h 1)
            (= sample-id-left (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (= h 1)
            (= sample-id-left (sample-id "KeysTop" "GETAOUT" "rr"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (> h 1)
            (= sample-id-left (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and
            (> h 1)
            (= sample-id-left (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
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
            (< <arg-GBLG-i> h)
            (or 
                (= sample-id-left sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
                (= sample-id-left sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_3"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_3"))
            )
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> (- h 1))
            (= sample-id-left (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> (- h 1))
            (= sample-id-left (sample-id "KeysTop" "GETAOUT" "rr"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
                    (= sample-id-left (sample-id "KeysBot" "GETAOUT" "r"))
                    (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
                    (= sample-id-left (sample-id "KeysBot" "GETAOUT" "rr"))
                    (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rin_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_0"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rout_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_0"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rin_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_1"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rout_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_1"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rin_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_2"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rout_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_2"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rin_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_3"))
        )
        (and 
            (= <arg-GBLG-i> h)
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "Sim" "GBLG" "rout_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_3"))
        )
        (and 
            (= <arg-GBLG-i> (+ h 1))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "r"))
        )
        (and 
            (= <arg-GBLG-i> (+ h 1))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "rr"))
        )
        (and 
            (= <arg-GBLG-i> (+ h 1))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
            (= sample-id-left (sample-id "LayeredEnc0" "LENCN" "r"))
            (= sample-id-right (sample-id "Enc" "ENCN" "r"))
        )
        (and 
            (= <arg-GBLG-i> (+ h 1))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
            (= sample-id-left (sample-id "LayeredEnc0" "LENCM" "r"))
            (= sample-id-right (sample-id "Enc" "ENCM" "r"))
        )
        (and 
            (> <arg-GBLG-i> (+ h 1))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
        )
        (and 
            (> <arg-GBLG-i> (+ h 1))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
        )
        (and 
            (> <arg-GBLG-i> (+ h 1))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
            (= sample-id-left (sample-id "LayeredEnc0" "LENCN" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCN" "r"))
        )
        (and 
            (> <arg-GBLG-i> (+ h 1))
            (= (- sample-ctr-left sample-ctr-old-left) (- sample-ctr-right sample-ctr-old-right))
            (= sample-id-left (sample-id "LayeredEnc0" "LENCM" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCM" "r"))
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
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i h)
                (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i j)))
            ) 
            (= (select state-left.KeysTop.z j) (select state-right.SimulatedLayersKeys.z (mk-tuple2 h j)))
            (= (select state-left.KeysBot.z j) (select state-right.KeysTop.z j))
            (= (select state-left.RealLayersKeys.z (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.z j))
            (=>
                (> i (+ h 2))
                (= (select state-left.RealLayersKeys.z (mk-tuple2 i j)) (select state-right.RealLayersKeys.z (mk-tuple2 i j)))
            )
        )
    )
)

(define-state-relation equal-T
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i h)
                (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i j)))
            )
            (= (select state-left.KeysTop.T j) (select state-right.SimulatedLayersKeys.T (mk-tuple2 h j)))
            (= (select state-left.KeysBot.T j) (select state-right.KeysTop.T j))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.T j))
            (=>
                (> i (+ h 2))
                (= (select state-left.RealLayersKeys.T (mk-tuple2 i j)) (select state-right.RealLayersKeys.T (mk-tuple2 i j)))
            )
        )
    )
)

(define-state-relation equal-flag
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i h)
                (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i j)))
            )
            (= (select state-left.KeysTop.flag j) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 h j)))
            (= (select state-left.KeysBot.flag j) (select state-right.KeysTop.flag j))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.flag j))
            (=>
                (> i (+ h 2))
                (= (select state-left.RealLayersKeys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
            )
        )
    )
)

(define-state-relation invariants
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (and
        (equal-z state-left state-right)
        (equal-T state-left state-right)
        (equal-flag state-left state-right)
    )
)

(define-state-relation invariant
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (invariants state-left state-right)
)

(define-lemma <relation-value-of-h-HybridIdeal-HybridReal1-SETBIT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_SETBIT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_SETBIT>)
        (j Int)
        (b Bool)
    )
    (= h -2)
)


(define-lemma <relation-value-of-h-HybridIdeal-HybridReal1-GETKEYSIN>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETKEYSIN>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETKEYSIN>)
        (j Int)
    )
    (= h 1)
)

(define-lemma <relation-value-of-h-HybridIdeal-HybridReal1-GETAOUT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (j Int)
    )
    (= h 1)
)

(define-lemma <relation-value-of-i-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (= i (+ h 1))
)

(define-lemma <relation-inv-case-i-lt-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- h 1))
        (and
            (= return-left.state.RealLayersKeys.flag old-state-left.RealLayersKeys.flag)
            (= return-left.state.KeysTop.flag old-state-left.KeysTop.flag)
            (= return-left.state.KeysBot.flag old-state-left.KeysBot.flag)
            (= return-right.state.RealLayersKeys.flag old-state-right.RealLayersKeys.flag)
            (= return-right.state.KeysTop.flag old-state-right.KeysTop.flag)
            (= return-right.state.KeysBot.flag old-state-right.KeysBot.flag)
            (= return-left.state.RealLayersKeys.T old-state-left.RealLayersKeys.T)
            (= return-left.state.KeysTop.T old-state-left.KeysTop.T)
            (= return-left.state.KeysBot.T old-state-left.KeysBot.T)
            (= return-right.state.RealLayersKeys.T old-state-right.RealLayersKeys.T)
            (= return-right.state.KeysTop.T old-state-right.KeysTop.T)
            (= return-right.state.KeysBot.T old-state-right.KeysBot.T)
            (= return-left.state.RealLayersKeys.z old-state-left.RealLayersKeys.z)
            (= return-left.state.KeysTop.z old-state-left.KeysTop.z)
            (= return-left.state.KeysBot.z old-state-left.KeysBot.z)
            (= return-right.state.RealLayersKeys.z old-state-right.RealLayersKeys.z)
            (= return-right.state.KeysTop.z old-state-right.KeysTop.z)
            (= return-right.state.KeysBot.z old-state-right.KeysBot.z)
        )
    )
)

(define-lemma <relation-inv-case-i-lt-hminusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- h 1))
        (invariants return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hminusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (- h 1))
        (invariants return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-h-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i h)
        (invariants return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ h 1))
        (invariants return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplustwo-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ h 2))
        (invariants return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i (+ h 2))
        (let
            (
                (r return-right.state.RealLayersKeys.r)
                (rr return-right.state.RealLayersKeys.rr)
            )
            (and
                (= return-left.state.RealLayersKeys.flag (store old-state-left.RealLayersKeys.flag (mk-tuple2 (+ i 1) j) (mk-some true)))
                (= return-left.state.SimulatedLayersKeys.flag old-state-left.SimulatedLayersKeys.flag)
                (= return-left.state.KeysTop.flag old-state-left.KeysTop.flag)
                (= return-left.state.KeysBot.flag old-state-left.KeysBot.flag)
                (= return-right.state.RealLayersKeys.flag (store old-state-right.RealLayersKeys.flag (mk-tuple2 (+ i 1) j) (mk-some true)))
                (= return-right.state.SimulatedLayersKeys.flag old-state-right.SimulatedLayersKeys.flag)
                (= return-right.state.KeysTop.flag old-state-right.KeysTop.flag)
                (= return-right.state.KeysBot.flag old-state-right.KeysBot.flag)

                (=>
                    (not (is-mk-none (select old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j))))
                    (= return-left.state.RealLayersKeys.T old-state-left.RealLayersKeys.T)
                )
                (=>
                    (is-mk-none (select old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j)))
                    (= return-left.state.RealLayersKeys.T
                        (store old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        )
                    )
                )
                (= return-left.state.SimulatedLayersKeys.T old-state-left.SimulatedLayersKeys.T)
                (= return-left.state.KeysTop.T old-state-left.KeysTop.T)
                (= return-left.state.KeysBot.T old-state-left.KeysBot.T)

                (=>
                    (not (is-mk-none (select old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j))))
                    (= return-right.state.RealLayersKeys.T old-state-right.RealLayersKeys.T)
                )
                (=>
                    (is-mk-none (select old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j)))
                    (= return-right.state.RealLayersKeys.T
                        (store old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        )
                    )
                )
                (= return-right.state.SimulatedLayersKeys.T old-state-right.SimulatedLayersKeys.T)
                (= return-right.state.KeysTop.T old-state-right.KeysTop.T)
                (= return-right.state.KeysBot.T old-state-right.KeysBot.T)

                (= return-left.state.RealLayersKeys.z old-state-left.RealLayersKeys.z)
                (= return-left.state.SimulatedLayersKeys.z old-state-left.SimulatedLayersKeys.z)
                (= return-left.state.KeysTop.z old-state-left.KeysTop.z)
                (= return-left.state.KeysBot.z old-state-left.KeysBot.z)
                (= return-right.state.RealLayersKeys.z old-state-right.RealLayersKeys.z)
                (= return-right.state.SimulatedLayersKeys.z old-state-right.SimulatedLayersKeys.z)
                (= return-right.state.KeysTop.z old-state-right.KeysTop.z)
                (= return-right.state.KeysBot.z old-state-right.KeysBot.z)
            )
        )
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i (+ h 2))
        (invariants return-left.state return-right.state)
    )
)

; i < h - 1
(define-lemma <relation-case-i-lt-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- h 1))
        (and
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 (+ i 1) j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 (+ i 1) j)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 (+ i 1) j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 (+ i 1) j)))
        )
    )
)

(define-lemma <relation-case-i-lt-hminusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (< i (- h 1))
        (= return-left.value return-right.value)
    )
)

; i = h - 1
(define-lemma <relation-case-i-is-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (- h 1))
        (and
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i r)))
            (= (select state-left.KeysTop.z j) (select state-right.SimulatedLayersKeys.z (mk-tuple2 h j)))
            (= (select state-left.KeysTop.T j) (select state-right.SimulatedLayersKeys.T (mk-tuple2 h j)))
        )
    )
)

(define-lemma <relation-case-i-is-hminusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (- h 1))
        (= return-left.value return-right.value)
    )
)

; i = h
(define-lemma <relation-case-i-is-h-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i h)
        (and
            (= (select state-left.KeysTop.z l) (select state-right.SimulatedLayersKeys.z (mk-tuple2 h l)))
            (= (select state-left.KeysTop.z r) (select state-right.SimulatedLayersKeys.z (mk-tuple2 h r)))
            (= (select state-left.KeysTop.flag l) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 h l)))
            (= (select state-left.KeysTop.flag r) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 h r)))
            (= (select state-left.KeysTop.T l) (select state-right.SimulatedLayersKeys.T (mk-tuple2 h l)))
            (= (select state-left.KeysTop.T r) (select state-right.SimulatedLayersKeys.T (mk-tuple2 h r)))
            (= (select state-left.KeysBot.z j) (select state-right.KeysTop.z j))
            (= (select state-left.KeysBot.T j) (select state-right.KeysTop.T j))
            (= (select state-left.KeysBot.flag j) (select state-right.KeysTop.flag j))
        )
    )
)

(define-lemma <relation-case-i-is-h-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i h)
        (= return-left.value return-right.value)
    )
)

; i = h + 1
(define-lemma <relation-case-i-is-hplusone-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ 1 h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 2 h) j)) (select state-right.KeysBot.flag j))
            (= (select state-left.KeysBot.flag l) (select state-right.KeysTop.flag l))
            (= (select state-left.KeysBot.flag r) (select state-right.KeysTop.flag r))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 2 h) j)) (select state-right.KeysBot.T j))
            (= (select state-left.KeysBot.T l) (select state-right.KeysTop.T l))
            (= (select state-left.KeysBot.T r) (select state-right.KeysTop.T r))
        )
    )
)

(define-lemma <relation-case-i-is-hplusone-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ h 1))
        (= return-left.value return-right.value)
    )
)
; i = h + 2
(define-lemma <relation-case-i-is-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ 2 h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i l)) (select state-right.KeysBot.flag l))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i r)) (select state-right.KeysBot.flag r))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i l)) (select state-right.KeysBot.T l))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i r)) (select state-right.KeysBot.T r))
        )
    )
)

(define-lemma <relation-case-i-is-hplustwo-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i (+ h 2))
        (= return-left.value return-right.value)
    )
)
; i > h + 2
(define-lemma <relation-case-i-gt-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i (+ 2 h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i l)) (select state-right.RealLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i r)) (select state-right.RealLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i l)) (select state-right.RealLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i r)) (select state-right.RealLayersKeys.T (mk-tuple2 i r)))
        )
    )
)

(define-lemma <relation-case-i-gt-hplustwo-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i (+ 2 h))
        (= return-left.value return-right.value)
    )

)

(define-lemma <relation-assume-all-invariants-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (invariants old-state-left old-state-right)
)

(define-lemma <relation-assert-all-invariants-HybridIdeal-HybridReal1-GBLG>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GBLG>)
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (invariants return-left.state return-right.state)
)

(assert 
    (=
        (<theorem-consts-HybridCircuitSecurity-h> <<theorem-consts>>)
        h
    )
)

(assert 
    (=
        (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>)
        d
    )
)

(assert 
    (=
        (<theorem-consts-HybridCircuitSecurity-hplusone> <<theorem-consts>>)
        hplusone
    )
)

; hplusone = h + 1
(assert 
    (= 
        hplusone
        (+ 1 h)
    )
)

; h > 0 for SETBIT and GETAOUT
(assert
    (> h 0)
)

; h < d for GETKEYSIN
(assert
    (< h d)
)