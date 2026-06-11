(define-fun randomness-mapping-NewKey
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 (sample-id "KX" "NewKey" "1"))
       (= id-1 (sample-id "PRF" "NewKey" "1"))))
