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
        (= sample-id-left (sample-id "pkg_Scheme_KEM" "KEM_GEN" "kem_gen"))
        (= sample-id-right (sample-id "pkg_Scheme_KEM" "KEM_GEN" "kem_gen"))
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
        (left-game <GameState_Hybrid2>)
        (right-game <GameState_CpaPkeIdealKemGame>)
    )
    (and 
        (rand-is-eq 
            (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (get-rand-ctr-hybrid2_1 (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (get-rand-ctr-game_1 (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
        )
        (rand-is-eq 
            (sample-id "pkg_CPA_KEM" "ENCAPS" "k")
            (sample-id "pkg_CPA_PKE_Ideal_KEM" "PKENC" "k")
            (get-rand-ctr-hybrid2_1 (sample-id "pkg_CPA_KEM" "ENCAPS" "k"))
            (get-rand-ctr-game_1 (sample-id "pkg_CPA_PKE_Ideal_KEM" "PKENC" "k"))
        )
    )
)
