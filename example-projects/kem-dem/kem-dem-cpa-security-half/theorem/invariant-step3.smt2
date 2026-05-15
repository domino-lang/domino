(define-state-relation invariant
    ((left-game <GameState_Hybrid0>)
     (right-game <GameState_Hybrid1>))
    (and (= left-game.CPA_KEM.pk right-game.Reduction_DEM.pk)
         (= (is-mk-none right-game.CPA_DEM.k) (is-mk-none left-game.CPA_KEM.c) (is-mk-none right-game.Reduction_DEM.c))))