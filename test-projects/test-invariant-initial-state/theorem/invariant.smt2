(define-fun invariant
    ((left <GameState_A>)
     (right <GameState_B>))
  Bool
  (= (<pkg-state-A-ctr> (<game-A-pkgstate-A> left))
     (<pkg-state-B-ctr> (<game-B-pkgstate-B> right))))
