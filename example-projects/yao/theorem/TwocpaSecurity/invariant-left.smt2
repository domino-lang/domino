(define-state-relation control-state (old via)
  (and
    (= old.keys_top.ActiveBit via.reduction.ActiveBit)
    (= old.keys_top.ActiveBitSetAndGenerated via.reduction.Generated)))

(define-state-relation key-state (old via)
  (forall ((h Int))
    (ite (= (select old.keys_top.ActiveBitSetAndGenerated h) (mk-some true))
      (let ((active (maybe-get (select old.keys_top.ActiveBit h)))
            (wire-keys (maybe-get (select old.keys_top.WireKey h))))
        (and
          (not (is-mk-none (select old.keys_top.ActiveBit h)))
          (not (is-mk-none (select old.keys_top.WireKey h)))
          (not (is-mk-none (select via.reduction.ActiveKey h)))
          (not (is-mk-none (select via.cpa.Key h)))
          (= (select wire-keys active)
             (select via.reduction.ActiveKey h))
          (= (select wire-keys (not active))
             (select via.cpa.Key h))))
      (and
        (is-mk-none (select old.keys_top.WireKey h))
        (is-mk-none (select via.reduction.ActiveKey h))
        (is-mk-none (select via.cpa.Key h))))))

(define-state-relation invariant (old via)
  (and
    (control-state old via)
    (key-state old via)))