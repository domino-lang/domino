(define-state-relation invariant
    ((left-game <GameState_Composition_Perfect_KEM_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
     (right-game <GameState_Hybrid1_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.Perfect_KEM.pk right-game.CCA_KEM.pk right-game.Reduction_KEM.pk)
        (= left-game.Perfect_KEM.sk right-game.CCA_KEM.sk)
        (= left-game.Perfect_KEM.k right-game.Reduction_KEM.k)
        (= left-game.Perfect_KEM.c right-game.Reduction_KEM.c)
        (= (is-mk-none left-game.Perfect_KEM.pk)
           (is-mk-none left-game.Perfect_KEM.sk)
           (is-mk-none right-game.Reduction_KEM.pk))
        (= (is-mk-none left-game.Perfect_KEM.c)
           (is-mk-none right-game.CCA_KEM.c))
        (=>
            (not (is-mk-none right-game.Reduction_KEM.c))
            (= (maybe-get right-game.CCA_KEM.c)
               (el2-1 (maybe-get right-game.Reduction_KEM.c))))))
