(define-lemma <case-i-is-one-GBLG>
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

(define-lemma <case-i-is-two-GBLG>
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

(define-lemma <case-i-gt-two-GBLG>
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

(define-lemma <abort-case-i-is-one-GBLG>
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

(define-lemma <abort-case-i-is-two-GBLG>
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

(define-lemma <abort-case-i-is-two-assumptions-GBLG>
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
            (= (select old-state-left.Keys.flag (mk-tuple2 2 l)) (select old-state-right.KeysBot.flag l))
            (= (select old-state-left.Keys.z (mk-tuple2 2 l)) (select old-state-right.KeysBot.z l))
            (= (select old-state-left.Keys.T (mk-tuple2 2 l)) (select old-state-right.KeysBot.T l))

            (= (select old-state-left.Keys.flag (mk-tuple2 2 r)) (select old-state-right.KeysBot.flag r))
            (= (select old-state-left.Keys.z (mk-tuple2 2 r)) (select old-state-right.KeysBot.z r))
            (= (select old-state-left.Keys.T (mk-tuple2 2 r)) (select old-state-right.KeysBot.T r))

            (= (select old-state-left.Keys.flag (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.flag (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.z (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.z (mk-tuple2 3 j)))
            (= (select old-state-left.Keys.T (mk-tuple2 3 j)) (select old-state-right.RealLayersKeys.T (mk-tuple2 3 j)))
        )
    )
)

(define-lemma <abort-case-i-gt-two-GBLG>
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
