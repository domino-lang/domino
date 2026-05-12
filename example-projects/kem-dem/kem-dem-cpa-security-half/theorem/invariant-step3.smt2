(define-state-relation invariant
    ((left-game <GameState_Hybrid0>)
     (right-game <GameState_Hybrid1>))
    (and (= left-game.pkg_CPA_KEM.pk right-game.pkg_Reduction_DEM.pk)
         (= left-game.pkg_CPA_KEM.ek right-game.pkg_Reduction_DEM.ek)
         (= (is-mk-none right-game.pkg_CPA_DEM.k) (is-mk-none right-game.pkg_Reduction_DEM.ek))))