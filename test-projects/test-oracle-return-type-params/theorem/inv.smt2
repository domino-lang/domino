(define-state-relation invariant (left right) true)

(define-fun randomness-mapping-Get
    ((sample-id-left SampleId) (sample-id-right SampleId)
     (sample-ctr-left Int) (sample-ctr-right Int))
    Bool
    false)

(define-fun randomness-mapping-Ping
    ((sample-id-left SampleId) (sample-id-right SampleId)
     (sample-ctr-left Int) (sample-ctr-right Int))
    Bool
    false)
