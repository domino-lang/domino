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

(define-fun equal-z
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    Bool
    (let 
        (
            (z-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (z-top-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysTop> state-right)))
            (z-bot-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (< i d)
                    (= (select z-left (mk-tuple2 i j)) (select z-sim-right (mk-tuple2 i j)))
                )
                (=>
                    (= i d)
                    (= (select z-left (mk-tuple2 i j)) (select z-top-right j))
                )
                (=>
                    (= i (+ d 1))
                    (= (select z-left (mk-tuple2 i j)) (select z-bot-right j))
                )
            )
        )
    )
)

(define-fun equal-T
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    Bool
    (let 
        (
            (T-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (T-top-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysTop> state-right)))
            (T-bot-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (< i d)
                    (= (select T-left (mk-tuple2 i j)) (select T-sim-right (mk-tuple2 i j)))
                )
                (=>
                    (= i d)
                    (= (select T-left (mk-tuple2 i j)) (select T-top-right j))
                )
                (=>
                    (= i (+ d 1))
                    (= (select T-left (mk-tuple2 i j)) (select T-bot-right j))
                )
            )
        )
    )
)

(define-fun equal-flag
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    Bool
    (let 
        (
            (flag-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-top-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysTop> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (< i d)
                    (= (select flag-left (mk-tuple2 i j)) (select flag-sim-right (mk-tuple2 i j)))
                )
                (=>
                    (= i d)
                    (= (select flag-left (mk-tuple2 i j)) (select flag-top-right j))
                )
                (=>
                    (= i (+ d 1))
                    (= (select flag-left (mk-tuple2 i j)) (select flag-bot-right j))
                )
            )
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    Bool
    (and
        (equal-z state-left state-right)
        (equal-T state-left state-right)
        (equal-flag state-left state-right)
    )
)

(define-fun <relation-case-i-lt-dminusone-CoreIdeal-LastHybrid-GBLG>
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
    Bool
    (=>
        (< i (- d 1))
        (=
            (<oracle-return-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-LayeredSimProxy-<$<!d!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort>  return-right)
        )
    )
)

(define-fun <relation-case-i-is-dminusone-CoreIdeal-LastHybrid-GBLG>
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
    Bool
    (=>
        (= i (- d 1))
        (=
            (<oracle-return-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-LayeredSimProxy-<$<!d!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort>  return-right)
        )
    )
)

(define-fun <relation-case-i-is-d-CoreIdeal-LastHybrid-GBLG>
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
    Bool
    (=>
        (= i d)
        (=
            (<oracle-return-CoreIdeal-<$<!n!><!m!><!p!><!w!><!d!>$>-LayeredSimProxy-<$<!d!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!d!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort>  return-right)
        )
    )
)

(assert 
    (=
        (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>)
        d
    )
)