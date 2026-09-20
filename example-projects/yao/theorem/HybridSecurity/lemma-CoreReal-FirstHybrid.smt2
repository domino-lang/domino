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
            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 2 l)) (select old-state-right.KeysBot.ActiveBit l))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 2 l)) (select old-state-right.KeysBot.WireKey l))

            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 2 r)) (select old-state-right.KeysBot.ActiveBit r))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 2 r)) (select old-state-right.KeysBot.WireKey r))

            (= (select old-state-left.Keys.ActiveBit (mk-tuple2 3 j)) (select old-state-right.LayeredKeys.ActiveBit (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.WireKey (mk-tuple2 3 j)) (select old-state-right.LayeredKeys.WireKey (mk-tuple2 3 j)))
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
