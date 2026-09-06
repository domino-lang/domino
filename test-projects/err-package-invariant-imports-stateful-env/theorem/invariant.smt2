(define-state-relation invariant (left right)
  (and
    (= left.ctr.ctr right.ctr.ctr)
    (= left.ctr.seen right.ctr.seen)
    (= left.src.calls right.src.calls)))
