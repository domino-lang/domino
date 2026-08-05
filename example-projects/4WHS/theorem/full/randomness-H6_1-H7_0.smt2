(define-fun randomness-mapping-Send2 
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 0)
   (= offset-1 0)
   (or (and (= id-0 (sample-id "Nonces" "Sample" "1"))
            (= id-1 (sample-id "Nonces" "Sample" "1")))
       (and (= id-0 (sample-id "PRF" "Eval" "1"))
            (= id-1 (sample-id "MAC" "Init" "1"))))))

(define-fun randomness-mapping-Send3
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 0)
   (= offset-1 0)
   (and (= id-0 (sample-id "PRF" "Eval" "1"))
        (= id-1 (sample-id "MAC" "Init" "1")))))
