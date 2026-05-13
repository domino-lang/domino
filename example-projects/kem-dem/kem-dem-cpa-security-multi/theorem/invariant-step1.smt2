(define-state-relation invariant
    ((left-game <GameState_CpaPkeGame>)
     (right-game <GameState_Hybrid0>))
    (= left-game.pkg_CPA_PKE.pk right-game.pkg_CPA_KEM.pk))