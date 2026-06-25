(define-state-relation invariant
    ((left-game <GameState_Hybrid0_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
     (right-game <GameState_Hybrid1_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>))
    (and (= left-game.CPA_KEM.pk right-game.Reduction_DEM.pk)
         (= (is-mk-none right-game.CPA_DEM.k) (is-mk-none left-game.CPA_KEM.c) (is-mk-none right-game.Reduction_DEM.c))))