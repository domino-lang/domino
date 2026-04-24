(define-fun randomness-mapping-Send1
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 (sample-id "Prot" "Run1" "1"))
       (= id-1 (sample-id "Nonces" "Sample" "1"))))

(define-fun randomness-mapping-Send2
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 (sample-id "Prot" "Run2" "1"))
       (= id-1 (sample-id "Nonces" "Sample" "1"))))
