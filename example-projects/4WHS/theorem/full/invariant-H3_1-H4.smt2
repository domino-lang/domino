(define-state-relation invariant
    ((state-H3  <GameState_H3_<$<!n!>$>>)
     (state-H4  <GameState_H4_<$<!n!>$>>))
  (and (= state-H3.KX state-H4.KX)
       (= state-H3.Nonces.Nonces state-H4.Nonces.Nonces)))
