(define-state-relation invariant
    ((left-game <GameState_Hybrid0>)
     (right-game <GameState_Hybrid1>))
    (= left-game.CPA_KEM.pk right-game.Reduction_DEM.pk))