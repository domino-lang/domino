; This oracle declares a literal `invariant`, so today's semantics apply:
; `ctr-eq` is just another state relation, not auto-proved as a claim unless
; explicitly declared in the theorem's lemmas {} block.

(define-fun invariant
    ((left <GameState_A>)
     (right <GameState_B>))
  Bool
  (= (<pkg-state-A-ctr> (<game-A-pkgstate-A> left))
     (<pkg-state-B-ctr> (<game-B-pkgstate-B> right))))

(define-state-relation ctr-eq (L R)
  (= L.A.ctr R.B.ctr))
