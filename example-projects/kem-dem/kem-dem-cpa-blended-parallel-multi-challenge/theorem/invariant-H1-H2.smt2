(define-state-relation invariant
    ((left-game <GameState_Hybrid0_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
     (right-game <GameState_Hybrid1_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>))
    (= left-game.CPA_KEM.pk right-game.Reduction_DEM.pk))