(define-state-relation invariant
    ((left-game)
     (right-game))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.Ideal_KEM.pk right-game.Reduction_DEM.pk)
        (= left-game.Ideal_KEM.sk right-game.Reduction_DEM.sk)
        (= left-game.Ideal_KEM.k right-game.CCA_DEM.k)
        (= left-game.Ideal_KEM.c right-game.Reduction_DEM.c)
        (= (is-mk-none left-game.Ideal_KEM.pk)
           (is-mk-none left-game.Ideal_KEM.sk))
        (= (is-mk-none left-game.Ideal_KEM.c)
           (is-mk-none right-game.Reduction_DEM.c)
           (is-mk-none right-game.CCA_DEM.c)
           (is-mk-none right-game.CCA_DEM.k))
        (=>
            (not (is-mk-none left-game.Ideal_KEM.c))
            (= (el2-2 (maybe-get left-game.Ideal_KEM.c))
               (maybe-get right-game.CCA_DEM.c)))))
