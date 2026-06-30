(define-fun randomness-mapping-Test
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 offset-1 0)
   (= id-0 (sample-id "Prf" "Eval" "1"))
   (= id-1 (sample-id "KX" "Test" "1"))))
