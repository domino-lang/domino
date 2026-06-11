(define-game-invariant
   (forall ((ctr Int))
          (let ((state (select game.KX.State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kid  (el10-4  (maybe-get state))))
                  (and (not (is-mk-none (select game.KX.Fresh ctr)))
                       (not (is-mk-none (select game.Prf.H kid)))
                       (= (select game.KX.Fresh ctr) (select game.Prf.H kid))))))))

