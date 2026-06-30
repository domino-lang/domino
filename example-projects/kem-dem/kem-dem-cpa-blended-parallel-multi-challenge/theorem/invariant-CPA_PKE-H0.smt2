(define-state-relation invariant
    ((left-game <GameState_Composition_CPA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
     (right-game <GameState_Hybrid0_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>))
    (= left-game.CPA_PKE.pk right-game.CPA_KEM.pk))