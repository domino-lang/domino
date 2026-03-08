(define-fun randomness-mapping-SAM
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
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (= 
                sample-id-left 
                ;TODO
            )
            (= 
                sample-id-right 
                ;TODO
            )
        )
        (and
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (=
                sample-id-left 
                ;TODO
            )
            (= sample-id-right 
                ;TODO
            )
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_Gweakprf>)
        (state-right <GameState_ModReduction1>)
    )
    Bool
    (let 
        (
            (k_left (<pkg-state-WeakPrf-k> (<game-Gweakprf-pkgstate-pkg_WeakPrf> state-left)))
            (k_right (<pkg-state-Prf-k> (<game-ModReduction1-pkgstate-pkg_Prf> state-right)))
        )
        ; TODO
    )
)