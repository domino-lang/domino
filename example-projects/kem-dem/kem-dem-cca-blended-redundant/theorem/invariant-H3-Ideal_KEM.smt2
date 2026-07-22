(define-state-relation invariant
    ((left-game)
     (right-game))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.CCA_KEM.pk left-game.Reduction_KEM.pk right-game.Ideal_KEM.pk)
        (= left-game.CCA_KEM.sk right-game.Ideal_KEM.sk)
        (= left-game.Reduction_KEM.k right-game.Ideal_KEM.k)
        (= left-game.Reduction_KEM.c right-game.Ideal_KEM.c)
        (= (is-mk-none left-game.CCA_KEM.pk)
           (is-mk-none left-game.CCA_KEM.sk))
        (= (is-mk-none left-game.CCA_KEM.c)
           (is-mk-none right-game.Ideal_KEM.c))
        (=>
            (not (is-mk-none left-game.Reduction_KEM.c))
            (= (maybe-get left-game.CCA_KEM.c)
               (el2-1 (maybe-get left-game.Reduction_KEM.c))))))
