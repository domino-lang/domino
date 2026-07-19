(define-state-relation invariant
    ((state-left) (state-right))
    (and (= state-left.KX     state-right.KX)
         (= state-left.Nonces state-right.Nonces)))
