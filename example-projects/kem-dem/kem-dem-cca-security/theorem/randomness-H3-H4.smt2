(define-fun randomness-mapping-PKGEN
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    (and
        (= sample-ctr-left sample-ctr-old-left)
        (= sample-ctr-right sample-ctr-old-right)
        (= sample-id-left (sample-id "Scheme_KEM" "KEM_GEN" "kem_gen"))
        (= sample-id-right (sample-id "Scheme_KEM" "KEM_GEN" "kem_gen"))
    )
)

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
    false
)

(define-state-relation relation-randomness
    (
        (left-game <GameState_Hybrid1>)
        (right-game <GameState_Hybrid2>)
    )
    (and
        (rand-is-eq
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (get-rand-ctr-H3 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (get-rand-ctr-H4 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
        )
        (rand-is-eq
            (sample-id "CCA_KEM" "ENCAPS" "k")
            (sample-id "CCA_DEM" "ENC" "k")
            (get-rand-ctr-H3 (sample-id "CCA_KEM" "ENCAPS" "k"))
            (get-rand-ctr-H4 (sample-id "CCA_DEM" "ENC" "k"))
        )
    )
)
