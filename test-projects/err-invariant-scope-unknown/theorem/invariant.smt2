; This fixture's actual point is the "with invariants [nonexistent-fragment]"
; reference in Eq.ssp, which names something that isn't a declared state
; relation at all.

(define-state-relation ctr-eq (L R)
  (= L.A.ctr R.B.ctr))
