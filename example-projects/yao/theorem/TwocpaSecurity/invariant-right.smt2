;; TwocpaViaCpa1 (via) == Twocpa1 (old)
;;
;; Mirror of invariant-left.smt2; see there for the reasoning.

(define-state-relation generated (via old)
  (forall ((h Int))
    (= (= (select via.reduction.Generated h) (mk-some true))
       (not (is-mk-none (select old.keys_top.WireKey h))))))

(define-state-relation control-state (via old)
  (and
    (= via.reduction.ActiveBit old.keys_top.ActiveBit)
    (generated via old)))

(define-state-relation key-state (via old)
  (forall ((h Int))
    (ite (not (is-mk-none (select old.keys_top.WireKey h)))
      (let ((active (maybe-get (select old.keys_top.ActiveBit h)))
            (wire-keys (maybe-get (select old.keys_top.WireKey h))))
        (and
          ;; GenerateWireKeys only generates the keys of h after SetActiveBit(h, .)
          (not (is-mk-none (select old.keys_top.ActiveBit h)))
          (not (is-mk-none (select via.reduction.ActiveKey h)))
          (not (is-mk-none (select via.cpa.Key h)))
          (= (select via.reduction.ActiveKey h)
             (select wire-keys active))
          (= (select via.cpa.Key h)
             (select wire-keys (not active)))))
      (and
        (is-mk-none (select via.reduction.ActiveKey h))
        (is-mk-none (select via.cpa.Key h))))))

(define-state-relation invariant (via old)
  (and
    (control-state via old)
    (key-state via old)))
