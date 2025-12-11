(define-fun randomness-mapping-ENC
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
            (= sample-id-left (sample-id "CPA" "ENC" "k"))
            (= sample-id-right (sample-id "Prf" "EVAL" "k"))
        )
        (and 
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (= sample-id-left (sample-id "Construction" "Enc" "r"))
            (= sample-id-right (sample-id "Coll" "GET_RAND" "x"))
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_Gcpa>)
        (state-right <GameState_Gmod_<$<!2!>$>>)
    )
    Bool
    (let 
        (
            (k_left (<pkg-state-CPA-k> (<game-Gcpa-pkgstate-CPA> state-left)))
            (k_right (<pkg-state-Prf-k> (<game-Gmod-<$<!2!>$>-pkgstate-Prf> state-right)))
        )
        (= k_left k_right)
    )
)
