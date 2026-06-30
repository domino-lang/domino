(define-fun randomness-mapping-NewKey
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 offset-1 0)
   (= id-0 (sample-id "KX" "NewKey" "1"))
   (= id-1 (sample-id "Prf" "NewKey" "1"))))
