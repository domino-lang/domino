(define-state-relation invariant
    ((left-game <GameState_Hybrid0>)
     (right-game <GameState_CpaPkeIdealKemGame>))
    (and (= left-game.pkg_CPA_KEM.pk right-game.pkg_CPA_PKE_Ideal_KEM.pk)
         (= left-game.pkg_CPA_KEM.ek right-game.pkg_CPA_PKE_Ideal_KEM.ek)))
