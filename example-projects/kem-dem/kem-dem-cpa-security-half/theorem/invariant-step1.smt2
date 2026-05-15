(define-state-relation invariant
    ((left-game <GameState_CpaPkeGame>)
     (right-game <GameState_Hybrid0>))
    (and (= left-game.pkg_CPA_PKE.pk right-game.pkg_CPA_KEM.pk)
         (= (is-mk-none left-game.pkg_CPA_PKE.c) (is-mk-none right-game.pkg_CPA_KEM.c))))