(define-fun randomness-mapping-PKENC
    ((sample-id-0 SampleId)
     (sample-id-1 SampleId)
     (offset-0 Int)
     (offset-1 Int))
  Bool
  (or
   (and
    (= sample-id-0 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
    (= sample-id-1 (sample-id "Scheme_KEM" "KEM_ENCAPS" "kem_encaps"))
    (= offset-0 offset-1 0))
   (and
    (= sample-id-0 (sample-id "CCA_KEM" "ENCAPS" "k"))
    (= sample-id-1 (sample-id "CCA_DEM" "ENC" "k"))
    (= offset-0 offset-1 0))))
