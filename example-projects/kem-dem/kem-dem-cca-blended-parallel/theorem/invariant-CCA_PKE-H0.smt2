(define-state-relation invariant
    ((left-game)
     (right-game))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.CCA_PKE.pk
           right-game.Correct_KEM.pk
           right-game.Reduction_Correct_KEM.pk)
        (= left-game.CCA_PKE.sk right-game.Correct_KEM.sk)
        (= left-game.CCA_PKE.c right-game.Reduction_Correct_KEM.c)
        (= (is-mk-none left-game.CCA_PKE.pk)
           (is-mk-none left-game.CCA_PKE.sk))
        (= (is-mk-none right-game.Correct_KEM.c)
           (is-mk-none right-game.Reduction_Correct_KEM.c))))