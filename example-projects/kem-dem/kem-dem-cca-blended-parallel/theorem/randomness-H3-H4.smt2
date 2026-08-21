(define-fun randomness-mapping-PKENC
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (or
    (and    (= offset-0 0)
            (= offset-1 0)
            (= id-0 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
            (= id-1 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps")))
    (and    (= offset-0 0)
            (= offset-1 0)
            (= id-0 (sample-id "CCA_KEM" "ENCAPS" "k"))
            (= id-1 (sample-id "CCA_DEM" "ENC"    "k")))
))
