;; TODO: this file still predates the LayeredKeys/Keys refactor.  It refers to
;; the package-state field `flag` and to `ActiveBitSetAndGenerated`, which no
;; longer exist, to the game instances `RealLayersKeys`/`SimulatedLayersKeys`,
;; which have been merged into a single `LayeredKeys`, and (in the randomness
;; mappings) to the eight coins `rin_round_*`/`rout_round_*` of the old
;; simulator, which now draws six (`rin_active`, `rout_active`, `rin_inactive`,
;; `rout_inactive`, `rout_zero_0`, `rout_zero_1`).  The names below have been
;; propagated mechanically; the statements themselves still need reworking.

(define-lemma <relation-case-i-is-one-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 1)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-two-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-gt-two-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i 2)
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-abort-case-i-is-one-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 1)
        (= ((_ is mk-abort) return-left.value)
           ((_ is mk-abort) return-right.value))
    )
)

(define-lemma <relation-abort-case-i-is-two-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
          (= ((_ is mk-abort) return-left.value)
              ((_ is mk-abort) return-right.value))
    )
)

(define-lemma <relation-abort-case-i-is-two-assumptions-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (= i 2)
        (and
            (= (select old-state-left.Keys.flag (mk-tuple2 2 l)) (select old-state-right.KeysBot.ActiveBitSetAndGenerated l))
            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 2 l)) (select old-state-right.KeysBot.ActiveBit l))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 2 l)) (select old-state-right.KeysBot.WireKey l))

            (= (select old-state-left.Keys.flag (mk-tuple2 2 r)) (select old-state-right.KeysBot.ActiveBitSetAndGenerated r))
            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 2 r)) (select old-state-right.KeysBot.ActiveBit r))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 2 r)) (select old-state-right.KeysBot.WireKey r))

            (= (select old-state-left.Keys.flag (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.flag (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.ActiveBit (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.WireKey (mk-tuple2 3 j)))
        )
    )
)

(define-lemma <relation-abort-case-i-gt-two-CoreReal-FirstHybrid-GarbleGate>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (> i 2)
          (= ((_ is mk-abort) return-left.value)
              ((_ is mk-abort) return-right.value))
    )
)
