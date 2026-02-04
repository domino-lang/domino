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
    true
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
    true
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
    true
)

(define-fun equal-z
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    Bool
    (let 
        (
            (z-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-CoreReal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (z-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-RealLayersKeys> state-right)))
            (z-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (z-top-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysTop> state-right)))
            (z-bot-right
                (<pkg-state-Keys-<$<!n!>$>-z> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (= i 1)
                    (= (select z-left (mk-tuple2 i j)) (select z-top-right j))
                )
                (=>
                    (= i 2)
                    (= (select z-left (mk-tuple2 i j)) (select z-bot-right j))
                )
                (=>
                    (> i 2)
                    (= (select z-left (mk-tuple2 i j)) (select z-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun equal-T
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    Bool
    (let 
        (
            (T-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-CoreReal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (T-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-RealLayersKeys> state-right)))
            (T-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (T-top-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysTop> state-right)))
            (T-bot-right
                (<pkg-state-Keys-<$<!n!>$>-T> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (= i 1)
                    (= (select T-left (mk-tuple2 i j)) (select T-top-right j))
                )
                (=>
                    (= i 2)
                    (= (select T-left (mk-tuple2 i j)) (select T-bot-right j))
                )
                (=>
                    (> i 2)
                    (= (select T-left (mk-tuple2 i j)) (select T-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun equal-flag
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    Bool
    (let 
        (
            (flag-left 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-CoreReal-<$<!n!><!m!><!p!><!w!><!d!>$>-pkgstate-Keys> state-left)))
            (flag-real-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-RealLayersKeys> state-right)))
            (flag-sim-right 
                (<pkg-state-LayeredKeys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-SimulatedLayersKeys> state-right)))
            (flag-top-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysTop> state-right)))
            (flag-bot-right
                (<pkg-state-Keys-<$<!n!>$>-flag> 
                    (<game-HybridReal-<$<!n!><!m!><!p!><!w!><!d!><!1!>$>-pkgstate-KeysBot> state-right)))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (= i 1)
                    (= (select flag-left (mk-tuple2 i j)) (select flag-top-right j))
                )
                (=>
                    (= i 2)
                    (= (select flag-left (mk-tuple2 i j)) (select flag-bot-right j))
                )
                (=>
                    (> i 2)
                    (= (select flag-left (mk-tuple2 i j)) (select flag-real-right (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-fun <relation-depth-is-positive-CoreReal-FirstHybrid-GETKEYSIN>
    (
        (old-state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (old-state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
        (return-left <OracleReturn_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>_LayerMap_<$<!d!><!n!>$>_GETKEYSIN>)
        (return-right <OracleReturn_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>_HybridLayerMap_<$<!d!><!h!><!n!><!p!>$>_GETKEYSIN>)
        (j Int)
    )
    Bool
    (> (<theorem-consts-CoreSecurity-d> <<theorem-consts>>) 0)
)

(define-fun invariant
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    Bool
    (and
        (equal-z state-left state-right)
        (equal-T state-left state-right)
        (equal-flag state-left state-right)
    
    )
)