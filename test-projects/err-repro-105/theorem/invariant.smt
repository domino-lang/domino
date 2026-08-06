(define-state-relation invariant (L R) true)

(define-fun randomness-mapping-Sample
  ( (stmt-left  Int) 
    (stmt-right  Int)
    (ctr-left Int)
    (ctr-right Int))
  Bool
  false
