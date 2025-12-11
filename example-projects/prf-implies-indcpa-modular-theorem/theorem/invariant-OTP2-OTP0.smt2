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
            (= sample-id-left (sample-id "Prf" "EVAL" "r"))
            (= sample-id-right (sample-id "Xor" "XOR" "pad"))
        )
        (and 
            (= sample-ctr-old-left sample-ctr-left)
            (= sample-ctr-old-right sample-ctr-right)
            (= sample-id-left (sample-id "Coll" "GET_RAND" "x"))
            (= sample-id-right (sample-id "Coll" "GET_RAND" "x"))
        )
    )
)

(define-fun invariant
    (
        (state-left <GameState_Gmod_<$<!2!>$>>)
        (state-right <GameState_Gmod_<$<!0!>$>>)
    )
    Bool
    (let
        (
            (T_Coll_left (<pkg-state-Coll-T> (<game-Gmod-<$<!2!>$>-pkgstate-Coll> state-left)))
            (T_Prf_left (<pkg-state-Prf-T> (<game-Gmod-<$<!2!>$>-pkgstate-Prf> state-left)))
            (T_Coll_right (<pkg-state-Coll-T> (<game-Gmod-<$<!0!>$>-pkgstate-Coll> state-right)))
        )
        (and 
            (forall 
                (
                    (x Bits_256)
                )
                (= 
                    ((_ is mk-none) (select T_Coll_left x))
                    ((_ is mk-none) (select T_Prf_left x))
                )
            )
            (= T_Coll_left T_Coll_right)
        )
    )
)
