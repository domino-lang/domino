(define-state-relation invariant
    ((left-game <GameState_CpaPkeGame>)
     (right-game <GameState_Hybrid2>))
    (and (= left-game.CPA_PKE.pk right-game.CPA_KEM.pk)
         (= (is-mk-none left-game.CPA_PKE.c) (is-mk-none right-game.CPA_KEM.c))))
