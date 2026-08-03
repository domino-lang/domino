(define-fun randomness-mapping-Query
  ((sample-id-left SampleId)
   (sample-id-right SampleId)
   (sample-ctr-left Int)
   (sample-ctr-right Int))
  Bool
  false)

(define-state-relation invariant (L R) true)
