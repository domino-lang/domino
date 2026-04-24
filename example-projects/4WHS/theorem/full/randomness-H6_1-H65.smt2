(define-fun randomness-mapping-Test
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 (sample-id "PRF" "Eval" "1"))
   (= id-1 (sample-id "KX" "Test" "1"))))
