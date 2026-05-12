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
    (and
        (= sample-ctr-left sample-ctr-old-left)
        (= sample-ctr-right sample-ctr-old-right)
        (= sample-id-left (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
        (= sample-id-right (sample-id "pkg_Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
    )
)