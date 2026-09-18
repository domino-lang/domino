(define-state-relation control-state (via old)
  (and
    (= via.reduction.ActiveBit old.keys_top.ActiveBit)
    (= via.reduction.Generated old.keys_top.ActiveBitSetAndGenerated)))

(define-state-relation key-state (via old)
  (forall ((h Int))
    (ite (= (select old.keys_top.ActiveBitSetAndGenerated h) (mk-some true))
      (let ((active (maybe-get (select old.keys_top.ActiveBit h)))
            (wire-keys (maybe-get (select old.keys_top.WireKey h))))
        (and
          (not (is-mk-none (select old.keys_top.ActiveBit h)))
          (not (is-mk-none (select old.keys_top.WireKey h)))
          (not (is-mk-none (select via.reduction.ActiveKey h)))
          (not (is-mk-none (select via.cpa.Key h)))
          (= (select via.reduction.ActiveKey h)
             (select wire-keys active))
          (= (select via.cpa.Key h)
             (select wire-keys (not active)))))
      (and
        (is-mk-none (select via.reduction.ActiveKey h))
        (is-mk-none (select via.cpa.Key h))
        (is-mk-none (select old.keys_top.WireKey h))))))

(define-state-relation invariant (via old)
  (and
    (control-state via old)
    (key-state via old)))