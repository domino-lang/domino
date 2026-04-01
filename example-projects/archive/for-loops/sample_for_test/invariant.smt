(define-fun randomness-mapping-Eval ((a Int) (b Int) (c Int) (d Int) (e Int) (f Int)) Bool false)

(define-fun invariant-Eval ((x CompositionState-Normal) (y CompositionState-Shifted) (z IntermediateState-Normal-pkg-Eval) (a IntermediateState-Shifted-pkg-Eval)) Bool true)
(define-fun foo
  (
    (old-state-left CompositionState-Normal)
    (old-state-right CompositionState-Shifted)
    (old-intstate-left IntermediateState-Normal-pkg-Eval)
    (old-intstate-right IntermediateState-Shifted-pkg-Eval)
    (return-left PartialReturn-Normal-pkg-Eval)
    (return-right PartialReturn-Shifted-pkg-Eval)
  )
  Bool
  true
)
