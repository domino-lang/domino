; Regression test: the invariant is unsatisfiable, so every per-oracle claim that assumes it
; holds succeeds vacuously. The only claim that can actually fail is the base case of the
; induction - that the invariant holds in the two games' initial states - which is exactly what
; this project is checking.
(define-fun invariant
    ((left <GameState_A>)
     (right <GameState_B>))
  Bool
  false)
