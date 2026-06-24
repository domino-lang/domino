(define-state-relation invariant
    ((left-game <GameState_Hybrid0_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
     (right-game <GameState_Composition_Perfect_KEM_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>))
    (and
        (= left-game.Scheme_KEM.st right-game.Scheme_KEM.st)
        (= left-game.Correct_KEM.pk left-game.Reduction_Correct_KEM.pk right-game.Perfect_KEM.pk)
        (= left-game.Correct_KEM.sk right-game.Perfect_KEM.sk)
        (= left-game.Correct_KEM.k right-game.Perfect_KEM.k)
        (= left-game.Reduction_Correct_KEM.c right-game.Perfect_KEM.c)
        (= (is-mk-none left-game.Correct_KEM.pk)
           (is-mk-none left-game.Correct_KEM.sk)
           (is-mk-none left-game.Reduction_Correct_KEM.pk))
        (= (is-mk-none left-game.Correct_KEM.c)
           (is-mk-none left-game.Reduction_Correct_KEM.c))
        (=>
            (not (is-mk-none left-game.Reduction_Correct_KEM.c))
            (= (maybe-get left-game.Correct_KEM.c)
               (el2-1 (maybe-get left-game.Reduction_Correct_KEM.c))))))
