; No relation here is literally named `invariant`, so domino treats each of
; these as an invariant fragment: their conjunction is assumed on the old
; state for every claim, and each is proved as its own claim on the new
; state (unless overridden in the theorem's lemmas {} block).

(define-state-relation ctr-eq (L R)
  (= L.A.ctr R.B.ctr))

(define-state-relation ctr-nonneg (L R)
  (and (>= L.A.ctr 0) (>= R.B.ctr 0)))

; True at the initial state (ctr starts at 0) but not preserved by Test
; (which always increments ctr) — proves that an explicit `admit` in the
; theorem's lemmas {} block overrides the auto-generated per-oracle claim
; for this fragment.
(define-state-relation ctr-broken (L R)
  (= L.A.ctr 0))
