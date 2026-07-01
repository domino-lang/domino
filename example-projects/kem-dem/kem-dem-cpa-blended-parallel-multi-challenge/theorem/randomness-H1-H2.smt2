(define-state-relation relation-randomness
    (
        (left-game <GameState_Hybrid0_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (right-game <GameState_Hybrid1_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
    )
    (and 
        (rand-is-eq 
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")
            (get-rand-ctr-H1 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (get-rand-ctr-H2 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
        )
        (rand-is-eq 
            (sample-id "CPA_KEM" "ENCAPS" "k")
            (sample-id "CPA_DEM" "ENC" "k")
            (get-rand-ctr-H1 (sample-id "CPA_KEM" "ENCAPS" "k"))
            (get-rand-ctr-H2 (sample-id "CPA_DEM" "ENC" "k"))
        )
    )
)
