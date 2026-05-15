(define-state-relation invariant
    ((left-game <GameState_Hybrid0>)
     (right-game <GameState_CpaPkeIdealKemGame>))
    (and (= left-game.CPA_KEM.pk right-game.CPA_PKE_Ideal_KEM.pk)
         (= (is-mk-none left-game.CPA_KEM.c) (is-mk-none right-game.CPA_PKE_Ideal_KEM.c))))
