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

(define-fun equal-z
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    Bool
    (let 
        (
            ; left
            (z-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (z-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (z-top-left
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (z-bot-left
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            ; right
            (z-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (z-top-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (z-bot-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=> ; needed for SETBIT and GETAOUT
                    (< i h)
                    (= (select z-sim-left (mk-tuple2 i j)) (select z-sim-right (mk-tuple2 i j)))
                ) 
                (= (select z-top-left j) (select z-sim-right (mk-tuple2 h j))) ; h ; needed for SETBIT and GETAOUT
                (= (select z-bot-left j) (select z-top-right j)) ; h + 1
                (= (select z-real-left (mk-tuple2 (+ h 2) j)) (select z-bot-right j)) ; h + 2
                (=>
                    (> i (+ h 2))
                    (= (select z-real-left (mk-tuple2 i j)) (select z-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun equal-T
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    Bool
    (let 
        (
            ; left
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (T-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (T-top-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (T-bot-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            ; right
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (T-top-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (T-bot-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=> ; needed for GETAOUT
                    (< i h)
                    (= (select T-sim-left (mk-tuple2 i j)) (select T-sim-right (mk-tuple2 i j)))
                )
                (= (select T-top-left j) (select T-sim-right (mk-tuple2 h j))) ; h ; needed for GETAOUT
                (= (select T-bot-left j) (select T-top-right j)) ; h + 1
                (= (select T-real-left (mk-tuple2 (+ h 2) j)) (select T-bot-right j)) ; h + 2 ; needed for GETKEYSIN
                (=> ; needed for GETKEYSIN
                    (> i (+ h 2))
                    (= (select T-real-left (mk-tuple2 i j)) (select T-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun equal-flag
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (flag-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (flag-top-left
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (flag-bot-left
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-top-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (< i h)
                    (= (select flag-sim-left (mk-tuple2 i j)) (select flag-sim-right (mk-tuple2 i j)))
                )
                (= (select flag-top-left j) (select flag-sim-right (mk-tuple2 h j))) ; h
                (= (select flag-bot-left j) (select flag-top-right j)) ; h + 1
                (= (select flag-real-left (mk-tuple2 (+ h 2) j)) (select flag-bot-right j)) ; h + 2 ; needed for GETKEYSIN
                (=> ; needed for GETKEYSIN
                    (> i (+ h 2))
                    (= (select flag-real-left (mk-tuple2 i j)) (select flag-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun invariants
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    Bool
    (and
        (equal-z state-left state-right)
        (equal-T state-left state-right)
        (equal-flag state-left state-right)
    )
)

(define-fun invariant
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    Bool
    (invariants state-left state-right)
)

(define-fun <relation-value-of-h-HybridIdeal-HybridReal1-SETBIT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_SETBIT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_SETBIT>)
        (j Int)
        (b Bool)
    )
    Bool
    (= h -2)
)


(define-fun <relation-value-of-h-HybridIdeal-HybridReal1-GETKEYSIN>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETKEYSIN>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETKEYSIN>)
        (j Int)
    )
    Bool
    (= h 1)
)

(define-fun <relation-value-of-h-HybridIdeal-HybridReal1-GETAOUT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (j Int)
    )
    Bool
    (= h 1)
)

(define-fun <relation-value-of-i-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (= i (+ h 1))
)

(define-fun <relation-inv-case-i-lt-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (< i (- h 1))
            (let 
                (
                    ; left
                    (flag-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (flag-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (flag-top-left
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (flag-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (flag-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (flag-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (flag-top-right
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (flag-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; left
                    (T-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (T-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (T-top-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (T-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (T-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (T-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (T-top-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (T-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; left
                    (z-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (z-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (z-top-left
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (z-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (z-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (z-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (z-top-right
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (z-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; old versions
                    (flag-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (flag-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (flag-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (flag-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (flag-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (flag-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (flag-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (flag-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                    (T-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (T-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (T-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (T-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (T-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (T-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (T-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (T-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                    (z-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (z-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (z-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (z-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (z-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (z-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (z-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (z-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                )
                (and
                    (= flag-real-left flag-real-left-old)
                    ;(= flag-sim-left flag-sim-left-old)
                    (= flag-top-left flag-top-left-old)
                    (= flag-bot-left flag-bot-left-old)
                    (= flag-real-right flag-real-right-old)
                    ;(= flag-sim-right flag-sim-right-old)
                    (= flag-top-right flag-top-right-old)
                    (= flag-bot-right flag-bot-right-old)
                    (= T-real-left T-real-left-old)
                    ;(= T-sim-left T-sim-left-old)
                    (= T-top-left T-top-left-old)
                    (= T-bot-left T-bot-left-old)
                    (= T-real-right T-real-right-old)
                    ;(= T-sim-right T-sim-right-old)
                    (= T-top-right T-top-right-old)
                    (= T-bot-right T-bot-right-old)
                    (= z-real-left z-real-left-old)
                    ;(= z-sim-left z-sim-left-old)
                    (= z-top-left z-top-left-old)
                    (= z-bot-left z-bot-left-old)
                    (= z-real-right z-real-right-old)
                    ;(= z-sim-right z-sim-right-old)
                    (= z-top-right z-top-right-old)
                    (= z-bot-right z-bot-right-old)
                )
            )
        )
    )
)

(define-fun <relation-inv-case-i-lt-hminusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (< i (- h 1))
            (invariants state-left state-right)
        )
    )
)

(define-fun <relation-inv-case-i-is-hminusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (= i (- h 1))
            (invariants state-left state-right)
        )
    )
)

(define-fun <relation-inv-case-i-is-h-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (= i h)
            (invariants state-left state-right)
        )
    )
)

(define-fun <relation-inv-case-i-is-hplusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (= i (+ h 1))
            (invariants state-left state-right)
        )
    )
)

(define-fun <relation-inv-case-i-is-hplustwo-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (= i (+ h 2))
            (invariants state-left state-right)
        )
    )
)

(define-fun <relation-inv-case-i-gt-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (> i (+ h 2))
            (let 
                (
                    ; left
                    (flag-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (flag-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (flag-top-left
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (flag-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (flag-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (flag-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (flag-top-right
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (flag-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-flag> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; left
                    (T-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (T-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (T-top-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (T-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (T-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (T-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (T-top-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (T-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; left
                    (z-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (z-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (z-top-left
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (z-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (z-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (z-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (z-top-right
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (z-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-z> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                    ; old versions
                    (flag-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (flag-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (flag-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (flag-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (flag-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (flag-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (flag-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (flag-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-flag>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                    (T-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (T-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (T-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (T-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (T-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (T-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (T-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (T-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-T>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                    (z-real-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> old-state-left)))
                    (z-sim-left-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> old-state-left)))
                    (z-top-left-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> old-state-left)))
                    (z-bot-left-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> old-state-left)))
                    (z-real-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> old-state-right)))
                    (z-sim-right-old
                        (<pkg-state-LayeredKeys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> old-state-right)))
                    (z-top-right-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> old-state-right)))
                    (z-bot-right-old
                        (<pkg-state-Keys-<$<!n!>$>-z>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> old-state-right)))
                    (r
                        (<pkg-state-LayeredKeys-<$<!n!>$>-r>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (rr
                        (<pkg-state-LayeredKeys-<$<!n!>$>-rr>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                )
                (and
                    (= flag-real-left (store flag-real-left-old (mk-tuple2 (+ i 1) j) (mk-some true)))
                    (= flag-sim-left flag-sim-left-old)
                    (= flag-top-left flag-top-left-old)
                    (= flag-bot-left flag-bot-left-old)
                    (= flag-real-right (store flag-real-right-old (mk-tuple2 (+ i 1) j) (mk-some true)))
                    (= flag-sim-right flag-sim-right-old)
                    (= flag-top-right flag-top-right-old)
                    (= flag-bot-right flag-bot-right-old)
                    ;(= T-real-left T-real-left-old)
                    (=>
                        (not (is-mk-none (select T-real-left-old (mk-tuple2 (+ i 1) j))))
                        (= T-real-left T-real-left-old)
                    )
                    (=>
                        (is-mk-none (select T-real-left-old (mk-tuple2 (+ i 1) j)))
                        (= T-real-left (store T-real-left-old (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store 
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        ))
                    )
                    (= T-sim-left T-sim-left-old)
                    (= T-top-left T-top-left-old)
                    (= T-bot-left T-bot-left-old)
                    ;(= T-real-right T-real-right-old)
                    (=>
                        (not (is-mk-none (select T-real-right-old (mk-tuple2 (+ i 1) j))))
                        (= T-real-right T-real-right-old)
                    )
                    (=>
                        (is-mk-none (select T-real-right-old (mk-tuple2 (+ i 1) j)))
                        (= T-real-right (store T-real-right-old (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store 
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        ))
                    )
                    (= T-sim-right T-sim-right-old)
                    (= T-top-right T-top-right-old)
                    (= T-bot-right T-bot-right-old)
                    (= z-real-left z-real-left-old)
                    (= z-sim-left z-sim-left-old)
                    (= z-top-left z-top-left-old)
                    (= z-bot-left z-bot-left-old)
                    (= z-real-right z-real-right-old)
                    (= z-sim-right z-sim-right-old)
                    (= z-top-right z-top-right-old)
                    (= z-bot-right z-bot-right-old)
                )
            )
        )
    )
)

(define-fun <relation-inv-case-i-gt-hplustwo-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (=>
            (> i (+ h 2))
            (invariants state-left state-right)
            ;(and
            ;    ;(equal-z state-left state-right)
            ;    (equal-T state-left state-right)
            ;    ;(equal-flag state-left state-right)
            ;)
        )
    )
)

; i < h - 1
(define-fun <relation-case-i-lt-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (z-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (flag-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (T-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
        )
        (=>
            (< i (- h 1))
            (and
                ; invariant
                (= (select z-sim-left (mk-tuple2 i l)) (select z-sim-right (mk-tuple2 i l)))
                (= (select z-sim-left (mk-tuple2 i r)) (select z-sim-right (mk-tuple2 i r)))
                (= (select flag-sim-left (mk-tuple2 i l)) (select flag-sim-right (mk-tuple2 i l)))
                (= (select flag-sim-left (mk-tuple2 i r)) (select flag-sim-right (mk-tuple2 i r)))
                (= (select T-sim-left (mk-tuple2 i l)) (select T-sim-right (mk-tuple2 i l)))
                (= (select T-sim-left (mk-tuple2 i r)) (select T-sim-right (mk-tuple2 i r)))

                (= (select z-sim-left (mk-tuple2 (+ i 1) j)) (select z-sim-right (mk-tuple2 (+ i 1) j)))
                (= (select T-sim-left (mk-tuple2 (+ i 1) j)) (select T-sim-right (mk-tuple2 (+ i 1) j)))
            )
        )
    )
)

(define-fun <relation-case-i-lt-hminusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (=>
        (< i (- h 1))
        (= 
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
    )
)

; i = h - 1
(define-fun <relation-case-i-is-hminusone-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (z-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (flag-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (T-sim-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
            (z-top-left
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (T-top-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
        )
        (=>
            (= i (- h 1))
            (and
                ; invariant
                (= (select z-sim-left (mk-tuple2 i l)) (select z-sim-right (mk-tuple2 i l)))
                (= (select z-sim-left (mk-tuple2 i r)) (select z-sim-right (mk-tuple2 i r)))
                (= (select flag-sim-left (mk-tuple2 i l)) (select flag-sim-right (mk-tuple2 i l)))
                (= (select flag-sim-left (mk-tuple2 i r)) (select flag-sim-right (mk-tuple2 i r)))
                (= (select T-sim-left (mk-tuple2 i l)) (select T-sim-right (mk-tuple2 i l)))
                (= (select T-sim-left (mk-tuple2 i r)) (select T-sim-right (mk-tuple2 i r)))

                (= (select z-top-left j) (select z-sim-right (mk-tuple2 h j)))
                (= (select T-top-left j) (select T-sim-right (mk-tuple2 h j)))
            )
        )
    )
)

(define-fun <relation-case-i-is-hminusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (=>
        (= i (- h 1))
        (= 
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
    )
)

; i = h
(define-fun <relation-case-i-is-h-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (T-bot-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (z-top-left
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (flag-top-left
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (T-top-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            (z-bot-left
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            (flag-bot-left
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            ; right
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-top-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (z-top-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (T-top-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
        )
        (=>
            (= i h)
            (and
                ; invariant
                (= (select z-top-left l) (select z-sim-right (mk-tuple2 h l))) 
                (= (select z-top-left r) (select z-sim-right (mk-tuple2 h r)))
                (= (select flag-top-left l) (select flag-sim-right (mk-tuple2 h l)))
                (= (select flag-top-left r) (select flag-sim-right (mk-tuple2 h r)))
                (= (select T-top-left l) (select T-sim-right (mk-tuple2 h l)))
                (= (select T-top-left r) (select T-sim-right (mk-tuple2 h r)))

                (= (select z-bot-left j) (select z-top-right j))
                (= (select T-bot-left j) (select T-top-right j)) 
                (= (select flag-bot-left j) (select flag-top-right j)) 
            )
        )
    )
)

(define-fun <relation-case-i-is-h-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (=>
        (= i h)
        (= 
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
    )
)

; i = h + 1
(define-fun <relation-case-i-is-hplusone-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            (flag-bot-left
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            (T-bot-left
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (T-bot-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (flag-top-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
            (T-top-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))

        )
        (=>
            (= i (+ 1 h))
            (and
                ; invariant
                (= (select flag-real-left (mk-tuple2 (+ 2 h) j)) (select flag-bot-right j))
                (= (select flag-bot-left l) (select flag-top-right l))
                (= (select flag-bot-left r) (select flag-top-right r))
                (= (select T-real-left (mk-tuple2 (+ 2 h) j)) (select T-bot-right j))
                (= (select T-bot-left l) (select T-top-right l))
                (= (select T-bot-left r) (select T-top-right r))
            )
        )
    )
)

(define-fun <relation-case-i-is-hplusone-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (=>
        (= i (+ h 1))
        (= 
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
    )
)
; i = h + 2
(define-fun <relation-case-i-is-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
            (T-bot-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
        )
        (=>
            (= i (+ 2 h))
            (and
                ; invariant
                (= (select flag-real-left (mk-tuple2 (+ 1 i) j)) (select flag-real-right (mk-tuple2 (+ 1 i) j)))
                (= (select flag-real-left (mk-tuple2 i l)) (select flag-bot-right l))
                (= (select flag-real-left (mk-tuple2 i r)) (select flag-bot-right r))
                (= (select T-real-left (mk-tuple2 (+ 1 i) j)) (select T-real-right (mk-tuple2 (+ 1 i) j)))
                (= (select T-real-left (mk-tuple2 i l)) (select T-bot-right l))
                (= (select T-real-left (mk-tuple2 i r)) (select T-bot-right r))
            )
        )
    )
)

(define-fun <relation-case-i-is-hplustwo-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (=>
        (= i (+ h 2))
        (= 
            (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
            (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
    )
)
; i > h + 2
(define-fun <relation-case-i-gt-hplustwo-assumptions-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            ; left
            (flag-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
            (T-real-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
            ; right
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
        )
        (=>
            (> i (+ 2 h))
            (and
                ; invariant
                (= (select flag-real-left (mk-tuple2 (+ 1 i) j)) (select flag-real-right (mk-tuple2 (+ 1 i) j)))
                (= (select flag-real-left (mk-tuple2 i l)) (select flag-real-right (mk-tuple2 i l)))
                (= (select flag-real-left (mk-tuple2 i r)) (select flag-real-right (mk-tuple2 i r)))
                (= (select T-real-left (mk-tuple2 (+ 1 i) j)) (select T-real-right (mk-tuple2 (+ 1 i) j)))
                (= (select T-real-left (mk-tuple2 i l)) (select T-real-right (mk-tuple2 i l)))
                (= (select T-real-left (mk-tuple2 i r)) (select T-real-right (mk-tuple2 i r)))
                ; rand map
                ;(rand-is-eq 
                ;    (sample-id "RealLayersKeys" "LGETKEYSOUT" "r")
                ;    (sample-id "RealLayersKeys" "LGETKEYSOUT" "r")
                ;    (get-rand-ctr-HybridIdeal (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
                ;    (get-rand-ctr-HybridReal1 (sample-id "RealLayersKeys" "LGETKEYSOUT" "r")))
                ;(rand-is-eq 
                ;    (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr")
                ;    (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr")
                ;    (get-rand-ctr-HybridIdeal (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
                ;    (get-rand-ctr-HybridReal1 (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr")))
                ;(rand-is-eq 
                ;    (sample-id "LayeredEnc0" "LENCM" "r")
                ;    (sample-id "LayeredEnc0" "LENCM" "r")
                ;    (+ 3 (get-rand-ctr-HybridIdeal (sample-id "LayeredEnc0" "LENCM" "r")))
                ;    (+ 3 (get-rand-ctr-HybridReal1 (sample-id "LayeredEnc0" "LENCM" "r"))))
            )
        )
    )
)

(define-fun <relation-case-i-gt-hplustwo-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (let 
            (
                ; left
                (flag-real-left 
                    (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                        (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))    
                ;(Z1-real-left 
                ;    (<pkg-state-LayeredKeys-<$<!n!>$>-Z1> 
                ;        (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                ;(Z-real-left 
                ;    (<pkg-state-LayeredKeys-<$<!n!>$>-Z> 
                ;        (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                ;(b-left
                ;    (<pkg-state-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-branch>
                ;    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-LayerMap> state-left)))
                (T-real-left 
                    (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                ; right
                (flag-real-right 
                    (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                        (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                ;(Z1-real-right 
                ;    (<pkg-state-LayeredKeys-<$<!n!>$>-Z1> 
                ;        (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                ;(Z-real-right 
                ;    (<pkg-state-LayeredKeys-<$<!n!>$>-Z> 
                ;        (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                ;(b-right
                ;    (<pkg-state-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-branch>
                ;    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-LayerMap> state-right)))
                (T-real-right 
                    (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
            )
            (=>
                (> i (+ 2 h))
                (and 
                    ;(= b-left b-right 1)
                    ;(= Z1-real-left Z1-real-right)
                    ;(= Z-real-left (maybe-get (select T-real-left (mk-tuple2 i r))))
                    ;(= Z-real-right (maybe-get (select T-real-right (mk-tuple2 i r))))
                    ;(= Z-real-left Z-real-right)
                    (= 
                        (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-left)
                        (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-return-value-or-abort> return-right))
                )
            )
        )
    )

)

(define-fun <relation-assume-all-invariants-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (invariants old-state-left old-state-right)
)

(define-fun <relation-assert-all-invariants-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        (invariants state-left state-right)
    )
)

(define-fun <relation-debug-HybridIdeal-HybridReal1-GBLG>
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
    Bool
    (let
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GBLG-game-state> return-right))
        )
        
        (let 
            (
                (x-left
                            (<pkg-state-Simgate-<$<!m!><!n!><!p!>$>-x>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-Sim> state-left)))
                (x-right
                            (<pkg-state-HybridLayeredSim-<$<!h!><!m!><!n!><!p!>$>-x>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-LayeredSim> state-right)))
                (y-left
                            (<pkg-state-Lev-<$<!n!>$>-y>
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-Lev> state-left)))
                (y-right
                            (<pkg-state-HybridLayeredLev-<$<!h!><!n!>$>-y>
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-LayeredLev> state-right)))
            )
            (=> (= 1 y-left) (= 1 y-right))
            ;(=> (= 1 x-left) (= 1 x-right))
        )
    )
)

(define-fun <relation-debug-invariant-HybridIdeal-HybridReal1-GETAOUT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (jj Int)
    )
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GETAOUT-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GETAOUT-game-state> return-right))
        )
        (and
            (equal-z state-left state-right)
            ;(equal-T state-left state-right)
            (let 
                (
                    ; left
                    (T-real-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-RealLayersKeys> state-left)))
                    (T-sim-left 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-SimulatedLayersKeys> state-left)))
                    (T-top-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    (T-bot-left
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysBot> state-left)))
                    ; right
                    (T-real-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-RealLayersKeys> state-right)))
                    (T-sim-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
                    (T-top-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysTop> state-right)))
                    (T-bot-right
                        (<pkg-state-Keys-<$<!n!>$>-T> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-KeysBot> state-right)))
                )
                (forall 
                    (
                        (i Int)
                        (j Int)
                    )
                    (and
                        (=> ; needed for GETAOUT
                            (< i h)
                            (= (select T-sim-left (mk-tuple2 i j)) (select T-sim-right (mk-tuple2 i j)))
                        )
                        (= (select T-top-left j) (select T-sim-right (mk-tuple2 h j))) ; h ; needed for GETAOUT
                        ;(= (select T-bot-left j) (select T-top-right j)) ; h + 1
                        (= (select T-real-left (mk-tuple2 (+ h 2) j)) (select T-bot-right j)) ; h + 2 ; needed for GETKEYSIN
                        (=> ; needed for GETKEYSIN
                            (> i (+ h 2))
                            (= (select T-real-left (mk-tuple2 i j)) (select T-real-right (mk-tuple2 i j)))
                        )
                    )
                )
            )
            ;(equal-flag state-left state-right)
        )
    )
)

(define-fun <relation-debug-rand-mapping-HybridIdeal-HybridReal1-GETAOUT>
    (
        (old-state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
        (return-left <OracleReturn_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETAOUT>)
        (jj Int)
    )
    Bool
    (let 
        (
            (state-left (<oracle-return-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GETAOUT-game-state> return-left))
            (state-right (<oracle-return-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-HybridLayerMap-<$<!d!><!h!><!n!><!p!>$>-GETAOUT-game-state> return-right))
        )
        true
            ;(let 
            ;    (
            ;        ; left
            ;        (r-left 
            ;            (<pkg-state-Keys-<$<!n!>$>-rr> 
            ;                (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
            ;        ; right
            ;        (r-right 
            ;            (<pkg-state-LayeredKeys-<$<!n!>$>-rr> 
            ;                (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            ;    )
            ;    (= r-left r-right)
            ;)
    )
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