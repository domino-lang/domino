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
        (state-left <GameState_ModReduction2>)
        (state-right <GameState_Gweakprf>)
    )
    Bool
    true
)