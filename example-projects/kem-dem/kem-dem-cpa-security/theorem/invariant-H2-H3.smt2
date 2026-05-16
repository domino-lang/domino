(define-state-relation invariant
    ((left-game <GameState_Composition_CPA_PKE_Ideal_KEM>)
     (right-game <GameState_Hybrid1>))
    (and (= left-game.CPA_PKE_Ideal_KEM.pk right-game.Reduction_DEM.pk)
         (= (is-mk-none left-game.CPA_PKE_Ideal_KEM.c)
            (is-mk-none right-game.CPA_DEM.k)
            (is-mk-none right-game.Reduction_DEM.c))))