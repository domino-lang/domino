(define-fun randomness-mapping-PKENC
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
            (= sample-id-left (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (= sample-id-right (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right))
        (and
            (= sample-id-left (sample-id "CCA_KEM" "ENCAPS" "k"))
            (= sample-id-right (sample-id "Ideal_KEM" "PKENC" "k"))
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)))
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
