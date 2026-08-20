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
            (= sample-id-left (sample-id "Ideal_KEM" "PKENC" "k"))
            (= sample-id-right (sample-id "CCA_DEM" "ENC" "k"))
            (= sample-offset-left 0)
            (= sample-offset-right 0))
    )
)