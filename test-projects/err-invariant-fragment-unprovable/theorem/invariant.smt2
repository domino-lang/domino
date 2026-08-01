; No relation here is literally named `invariant`, so domino treats each of
; these as an invariant fragment: their conjunction is assumed on the old
; state for every claim, and each is proved as its own claim on the new
; state (unless overridden in the theorem's lemmas {} block).

(define-state-relation ctr-eq (L R)
  (= L.A.ctr R.B.ctr))

(define-state-relation ctr-nonneg (L R)
  (and (>= L.A.ctr 0) (>= R.B.ctr 0)))

; True at the initial state (ctr starts at 0) but not preserved by Test
; (which always increments ctr): the auto-generated per-oracle claim for
; this fragment must fail, and specifically be reported against the claim
; name "ctr-broken" rather than a generic "invariant" failure.
(define-state-relation ctr-broken (L R)
  (= L.A.ctr 0))
