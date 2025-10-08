(define-fun invariant
  ( (l <GameState_Simple>)
    (r <GameState_Simple>))
  Bool
  true)

(define-fun randomness-mapping-Sample
  ( (base-ctr-left Int) 
    (base-ctr-right Int)
    (stmt-left  SampleId) 
    (stmt-right  SampleId)
    (ctr-left Int)
    (ctr-right Int))
  Bool
  (and
    (= stmt-left  (sample-id "simple" "Sample" "first"))
    (= stmt-right (sample-id "simple" "Sample" "second"))
    (= (- ctr-left  base-ctr-left)
       (- ctr-right base-ctr-right))))
