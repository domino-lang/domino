(define-game-invariant
   (and
    (< (- 1) game.rand.ctr)
    ;This is some illegal SMT-code which someone maliciously tries to hide in the invariant
    (forall ((i Int))
    (= (<<func-f>> i) 0)
    )
))

