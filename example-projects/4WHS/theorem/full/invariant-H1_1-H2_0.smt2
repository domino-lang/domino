(define-state-relation invariant
    ((state-left  <GameState_H1_<$<!n!>$>>)
     (state-right <GameState_H2_<$<!n!>$>>))
    (and (= state-left.KX     state-right.KX)
         (= state-left.Nonces state-right.Nonces)))
