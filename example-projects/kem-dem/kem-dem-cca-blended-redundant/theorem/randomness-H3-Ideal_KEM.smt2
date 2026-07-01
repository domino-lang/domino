(define-fun randomness-mapping-PKENC
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (or
        (and
            (= sample-id-left (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (= sample-id-right (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (= sample-offset-left 0)
            (= sample-offset-right 0))
        (and
            (= sample-id-left (sample-id "CCA_KEM" "ENCAPS" "k"))
            (= sample-id-right (sample-id "Ideal_KEM" "PKENC" "k"))
            (= sample-offset-left 0)
            (= sample-offset-right 0))
    )
)

(define-state-relation relation-randomness
    (
        (left-game <GameState_Hybrid1_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (right-game <GameState_Composition_Ideal_KEM_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
    )
    (and
        (rand-is-eq
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (get-rand-ctr-H3 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (get-rand-ctr-Ideal_KEM (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
        )
        (rand-is-eq
            (sample-id "CCA_KEM" "ENCAPS" "k")
            (sample-id "Ideal_KEM" "PKENC" "k")
            (get-rand-ctr-H3 (sample-id "CCA_KEM" "ENCAPS" "k"))
            (get-rand-ctr-Ideal_KEM (sample-id "Ideal_KEM" "PKENC" "k"))
        )
    )
)
