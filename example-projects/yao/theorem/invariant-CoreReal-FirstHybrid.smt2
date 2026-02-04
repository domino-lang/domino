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
                    true
                    (= (select z-left (mk-tuple2 i j)) (select z-top-right j))
                )
                ;(=>
                ;    (not (= i 1))
                ;    (= (select z-left (mk-tuple2 i j)) (select z-top-right j))
                ;)
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
                    true
                    (= (select T-left (mk-tuple2 i j)) (select T-top-right j))
                )
                ;(=>
                ;    (not (= i 1))
                ;    (= (select z-left (mk-tuple2 i j)) (select z-top-right j))
                ;)
            )
        )
    )
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
    )
)