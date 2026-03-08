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
            (= sample-id-left 
                ;TODO
            )
            (= sample-id-right 
                ;TODO
            )
        )
        (and
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (= sample-id-left 
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
        (state-left <GameState_ModReduction1>)
        (state-right <GameState_ModReduction2>)
    )
    Bool
    (let 
        (
            (T_left (<pkg-state-Prf-T> (<game-ModReduction1-pkgstate-pkg_Prf> state-left)))
            (T_reduction_right (<pkg-state-Reduction2-T> (<game-ModReduction2-pkgstate-reduction2> state-right)))
            (T_coll_right (<pkg-state-Coll-T> (<game-ModReduction2-pkgstate-pkg_Coll> state-right)))
        )
        (and
            ;TODO
        )
    )
)