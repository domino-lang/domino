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
    false
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

(define-fun invariant
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
            (let 
                (
                    ; left
                    (r-left 
                        (<pkg-state-Keys-<$<!n!>$>-rr> 
                            (<game-HybridIdeal-<$<!n!><!m!><!p!><!w!><!d!><!h!>$>-pkgstate-KeysTop> state-left)))
                    ; right
                    (r-right 
                        (<pkg-state-LayeredKeys-<$<!n!>$>-rr> 
                            (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>-pkgstate-SimulatedLayersKeys> state-right)))

                )
                (= r-left r-right)
            )
    )
)

(assert 
    (=
        (<theorem-consts-CoreSecurity-h> <<theorem-consts>>)
        h
    )
)

(assert 
    (=
        (<theorem-consts-CoreSecurity-d> <<theorem-consts>>)
        d
    )
)

(assert 
    (=
        (<theorem-consts-CoreSecurity-hplusone> <<theorem-consts>>)
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