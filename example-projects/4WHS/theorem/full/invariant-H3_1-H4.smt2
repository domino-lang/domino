(define-fun invariant
    ((state-H3  <GameState_H3_<$<!n!>$>>)
     (state-H4  <GameState_H4_<$<!n!>$>>))
  Bool
  (and (= (<game-H3-<$<!n!>$>-pkgstate-KX> state-H3)
          (<game-H4-<$<!n!>$>-pkgstate-KX> state-H4))
       (= (<pkg-state-Nonces-<$<!n!>$>-Nonces> (<game-H3-<$<!n!>$>-pkgstate-Nonces> state-H3))
	      (<pkg-state-Nonces-<$<!n!>$>-Nonces> (<game-H4-<$<!n!>$>-pkgstate-Nonces> state-H4)))))
