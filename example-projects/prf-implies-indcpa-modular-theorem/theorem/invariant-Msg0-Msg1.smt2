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
            (= sample-id-left (sample-id "Coll" "GET_RAND" "x"))
            (= sample-id-right (sample-id "Coll" "GET_RAND" "x"))
        )
        (and 
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (= sample-id-left (sample-id "Xor" "XOR" "r"))
            (= sample-id-right (sample-id "Xor" "XOR" "r"))
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_Gmod_<$<!1!>$>>)
        (state-right <GameState_Gmod_<$<!1!>$>>)
    )
    Bool
    (let
        (
            (T_left (<pkg-state-Coll-T> (<game-Gmod-<$<!1!>$>-pkgstate-Coll> state-left)))
            (T_right (<pkg-state-Coll-T> (<game-Gmod-<$<!1!>$>-pkgstate-Coll> state-right)))
        )
        (= T_left T_right)
    )
)
