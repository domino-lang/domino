(define-state-relation invariant
    ((left-game <GameState_Composition_CPA_PKE>)
     (right-game <GameState_Hybrid0>))
    (= left-game.CPA_PKE.pk right-game.CPA_KEM.pk))