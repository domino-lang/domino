(define-fun invariant
    ((state-left  <GameState_H0_<$<!n!>$>>)
     (state-right <GameState_H1_<$<!n!>$>>))
  Bool
  (= (<game-H0-<$<!n!>$>-pkgstate-KX> state-left)    
     (<game-H1-<$<!n!>$>-pkgstate-KX> state-right)))
