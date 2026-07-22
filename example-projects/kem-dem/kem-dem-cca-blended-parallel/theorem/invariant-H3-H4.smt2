(define-state-relation invariant
    ((left-game)
     (right-game))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.CCA_KEM.pk left-game.Reduction_KEM.pk right-game.Reduction_DEM.pk)
        (= left-game.CCA_KEM.sk right-game.Reduction_DEM.sk)
        (= left-game.Reduction_KEM.c right-game.Reduction_DEM.c)
        (= left-game.Reduction_KEM.k right-game.CCA_DEM.k)
        (= (is-mk-none left-game.CCA_KEM.pk)
           (is-mk-none left-game.CCA_KEM.sk))
        (= (is-mk-none left-game.CCA_KEM.c)
           (is-mk-none right-game.Reduction_DEM.c)
           (is-mk-none right-game.CCA_DEM.k)
           (is-mk-none right-game.CCA_DEM.c))
        (=>
            (not (is-mk-none left-game.Reduction_KEM.c))
            (and
                (= (maybe-get left-game.CCA_KEM.c)
                   (el2-1 (maybe-get left-game.Reduction_KEM.c)))
                (= (maybe-get right-game.CCA_DEM.c)
                   (el2-2 (maybe-get right-game.Reduction_DEM.c)))))))