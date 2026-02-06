(define-fun invariant
    ((state-left  <GameState_H1_<$<!n!>$>>)
     (state-right <GameState_H2_<$<!n!>$>>))
  Bool
  (let ((pkg-state-KX-left (<game-H1-<$<!n!>$>-pkgstate-KX> state-left))
        (pkg-state-KX-right (<game-H2-<$<!n!>$>-pkgstate-KX> state-right))
        (pkg-state-Nonces-left (<game-H1-<$<!n!>$>-pkgstate-Nonces> state-left))
        (pkg-state-Nonces-right (<game-H2-<$<!n!>$>-pkgstate-Nonces> state-right)))
    (and (= pkg-state-KX-left pkg-state-KX-right)
         (= pkg-state-Nonces-left pkg-state-Nonces-right))))
