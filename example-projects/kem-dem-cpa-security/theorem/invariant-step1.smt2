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
    (or
        (and
            (= sample-ctr-left sample-ctr-old-left)
            (= sample-ctr-right sample-ctr-old-right)
            (= sample-id-left (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
            (= sample-id-right (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
        )
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
    (and
     (= sample-ctr-left sample-ctr-old-left)
     (= sample-ctr-right sample-ctr-old-right)
     (= sample-id-left sample-id-right)))

(define-state-relation relation-randomness
    (
        (left-game <GameState_PkeCpaGame>)
        (right-game <GameState_Hybrid0>)
    )
    (and 
        (rand-is-eq 
            (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc")
            (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc")
            (get-rand-ctr-pke_cpa_0 (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
            (get-rand-ctr-hybrid0_0 (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
        )
        (rand-is-eq 
            (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps")
            (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps")
            (get-rand-ctr-pke_cpa_0 (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
            (get-rand-ctr-hybrid0_0 (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
        )
    )
)

(define-state-relation invariant
    (
        (left-game <GameState_PkeCpaGame>)
        (right-game <GameState_Hybrid0>)
    )
    (and 
        (= left-game.pkg_PKE_CPA.pk right-game.pkg_KEM_CPA.pk)
        (= left-game.pkg_PKE_CPA.ek right-game.pkg_KEM_CPA.ek)
    )
)
