(define-fun invariant
  ( (l <GameState_Simple>)
    (r <GameState_Simple>))
  Bool
  true)

(define-fun randomness-mapping-Sample
  ( (base-ctr-left Int) 
    (base-ctr-right Int)
    (stmt-left  Int) 
    (stmt-right  Int)
    (ctr-left Int)
    (ctr-right Int))
  Bool
  false
