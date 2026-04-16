(define-fun randomness-mapping-Query
  ((rand-ctr-left Int)
   (rand-ctr-right Int)
   (sample-id-left SampleId)
   (sample-id-right SampleId)
   (sample-ctr-left Int)
   (sample-ctr-right Int))
  Bool
  false)

(define-fun invariant
  ((state-left <GameState_GameSplit>)
   (state-right <GameState_GameTmp>))
  Bool
  true)
