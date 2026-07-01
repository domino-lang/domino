(define-fun randomness-mapping-Send1
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 (sample-id "Prot" "Run1" "1"))
       (= id-1 (sample-id "Nonces" "Sample" "1"))))

(define-fun randomness-mapping-Send2
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 (sample-id "Prot" "Run2" "1"))
       (= id-1 (sample-id "Nonces" "Sample" "1"))))
