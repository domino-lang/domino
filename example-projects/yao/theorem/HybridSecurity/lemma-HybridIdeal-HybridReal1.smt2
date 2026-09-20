(define-lemma <relation-generate-h0-old-layer1-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (and (> old-state-left.d 1) (= old-state-left.h 0))
        (and
            (= (select old-state-left.LayeredKeys.WireKey (mk-tuple2 1 wire))
               (select old-state-right.KeysTop.WireKey wire))
            (= (select old-state-left.LayeredKeys.ActiveBit (mk-tuple2 1 wire))
               (select old-state-right.KeysTop.ActiveBit wire))
        )
    )
)

(define-lemma <relation-generate-old-layered-layer1-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (or
            (<= old-state-left.d 1)
            (and (not (= old-state-left.h 0)) (not (= old-state-left.h 1)))
        )
        (and
            (= (select old-state-left.LayeredKeys.WireKey (mk-tuple2 1 wire))
               (select old-state-right.LayeredKeys.WireKey (mk-tuple2 1 wire)))
            (= (select old-state-left.LayeredKeys.ActiveBit (mk-tuple2 1 wire))
               (select old-state-right.LayeredKeys.ActiveBit (mk-tuple2 1 wire)))
        )
    )
)

(define-lemma <relation-generate-h0-layer1-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (and (> old-state-left.d 1) (= old-state-left.h 0))
        (and
            (= (select return-left.state.LayeredKeys.WireKey (mk-tuple2 1 wire))
               (select return-right.state.KeysTop.WireKey wire))
            (= (select return-left.state.LayeredKeys.ActiveBit (mk-tuple2 1 wire))
               (select return-right.state.KeysTop.ActiveBit wire))
        )
    )
)

(define-lemma <relation-generate-layered-layer1-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (or
            (<= old-state-left.d 1)
            (and (not (= old-state-left.h 0)) (not (= old-state-left.h 1)))
        )
        (and
            (= (select return-left.state.LayeredKeys.WireKey (mk-tuple2 1 wire))
               (select return-right.state.LayeredKeys.WireKey (mk-tuple2 1 wire)))
            (= (select return-left.state.LayeredKeys.ActiveBit (mk-tuple2 1 wire))
               (select return-right.state.LayeredKeys.ActiveBit (mk-tuple2 1 wire)))
        )
    )
)

(define-lemma <relation-inv-generate-h-is-zero-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (= old-state-left.h 0)
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-generate-h-is-one-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (= old-state-left.h 1)
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-generate-h-is-other-Hybrid$true$-Hybrid$false$+-GenerateInputWireKeys>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (wire Int)
    )
    (=>
        (and (not (= old-state-left.h 0)) (not (= old-state-left.h 1)))
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-lt-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (< i (- old-state-left.h 1))
        )
        (and
            (= return-left.state.KeysTop.WireKey old-state-left.KeysTop.WireKey)
            (= return-left.state.KeysBot.WireKey old-state-left.KeysBot.WireKey)
            (= return-right.state.KeysTop.WireKey old-state-right.KeysTop.WireKey)
            (= return-right.state.KeysBot.WireKey old-state-right.KeysBot.WireKey)
            (= return-left.state.KeysTop.ActiveBit old-state-left.KeysTop.ActiveBit)
            (= return-left.state.KeysBot.ActiveBit old-state-left.KeysBot.ActiveBit)
            (= return-right.state.KeysTop.ActiveBit old-state-right.KeysTop.ActiveBit)
            (= return-right.state.KeysBot.ActiveBit old-state-right.KeysBot.ActiveBit)
        )
    )
)

(define-lemma <relation-inv-case-i-lt-hminusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (< i (- old-state-left.h 1))
        )
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hminusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (= i (- old-state-left.h 1))
        )
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-h-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (= i old-state-left.h)
        )
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (= i (+ old-state-left.h 1))
        )
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplustwo-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (= i (+ old-state-left.h 2))
        )
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (> i (+ old-state-left.h 2))
        )
        (and
            (= return-left.state.KeysTop.WireKey old-state-left.KeysTop.WireKey)
            (= return-left.state.KeysBot.WireKey old-state-left.KeysBot.WireKey)
            (= return-right.state.KeysTop.WireKey old-state-right.KeysTop.WireKey)
            (= return-right.state.KeysBot.WireKey old-state-right.KeysBot.WireKey)
            (= return-left.state.KeysTop.ActiveBit old-state-left.KeysTop.ActiveBit)
            (= return-left.state.KeysBot.ActiveBit old-state-left.KeysBot.ActiveBit)
            (= return-right.state.KeysTop.ActiveBit old-state-right.KeysTop.ActiveBit)
            (= return-right.state.KeysBot.ActiveBit old-state-right.KeysBot.ActiveBit)
        )
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and
            (> old-state-left.d 0)
            (>= i 1)
            (< i old-state-left.d)
            (> i (+ old-state-left.h 2))
        )
        (invariant return-left.state return-right.state)
    )
)

; i < h - 1
(define-lemma <relation-case-i-lt-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (< i (- state-left.h 1)))
        (and
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i r)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i r)))
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 (+ i 1) j)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 (+ i 1) j)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 (+ i 1) j)) (select state-right.LayeredKeys.WireKey (mk-tuple2 (+ i 1) j)))
        )
    )
)

(define-lemma <relation-case-i-lt-hminusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (< i (- old-state-left.h 1)))
        (= return-left.value return-right.value)
    )
)

; i = h - 1
(define-lemma <relation-case-i-is-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (= i (- state-left.h 1)))
        (and
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i r)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i r)))
            (=>
                (< state-left.h state-left.d)
                (and
                    (= (select state-left.KeysTop.ActiveBit j) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 state-left.h j)))
                    (= (select state-left.KeysTop.WireKey j) (select state-right.LayeredKeys.WireKey (mk-tuple2 state-left.h j)))
                )
            )
            (=>
                (>= state-left.h state-left.d)
                (and
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 state-left.h j)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 state-left.h j)))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 state-left.h j)) (select state-right.LayeredKeys.WireKey (mk-tuple2 state-left.h j)))
                )
            )
        )
    )
)

(define-lemma <relation-case-i-is-hminusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (= i (- old-state-left.h 1)))
        (= return-left.value return-right.value)
    )
)

; i = h
(define-lemma <relation-case-i-is-h-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (= i state-left.h))
        (and
            (= (select state-left.KeysTop.ActiveBit l) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 state-left.h l)))
            (= (select state-left.KeysTop.ActiveBit r) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 state-left.h r)))
            (= (select state-left.KeysTop.WireKey l) (select state-right.LayeredKeys.WireKey (mk-tuple2 state-left.h l)))
            (= (select state-left.KeysTop.WireKey r) (select state-right.LayeredKeys.WireKey (mk-tuple2 state-left.h r)))
            (=>
                (< state-left.h (- state-left.d 1))
                (and
                    (= (select state-left.KeysBot.ActiveBit j) (select state-right.KeysTop.ActiveBit j))
                    (= (select state-left.KeysBot.WireKey j) (select state-right.KeysTop.WireKey j))
                )
            )
            (=>
                (= state-left.h (- state-left.d 1))
                (and
                    (= (select state-left.KeysBot.ActiveBit j) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 (+ state-left.h 1) j)))
                    (= (select state-left.KeysBot.WireKey j) (select state-right.LayeredKeys.WireKey (mk-tuple2 (+ state-left.h 1) j)))
                )
            )
        )
    )
)

(define-lemma <relation-case-i-is-h-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (= i old-state-left.h))
        (= return-left.value return-right.value)
    )
)

; i = h + 1
(define-lemma <relation-case-i-is-hplusone-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (= i (+ 1 state-left.h)))
        (and
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 (+ 2 state-left.h) j)) (select state-right.KeysBot.ActiveBit j))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 (+ 2 state-left.h) j)) (select state-right.KeysBot.WireKey j))
            (=>
                (= state-left.h 0)
                (and
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.KeysTop.ActiveBit l))
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.KeysTop.ActiveBit r))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.KeysTop.WireKey l))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.KeysTop.WireKey r))
                )
            )
            (=>
                (> state-left.h 0)
                (and
                    (= (select state-left.KeysBot.ActiveBit l) (select state-right.KeysTop.ActiveBit l))
                    (= (select state-left.KeysBot.ActiveBit r) (select state-right.KeysTop.ActiveBit r))
                    (= (select state-left.KeysBot.WireKey l) (select state-right.KeysTop.WireKey l))
                    (= (select state-left.KeysBot.WireKey r) (select state-right.KeysTop.WireKey r))
                )
            )
        )
    )
)

(define-lemma <relation-case-i-is-hplusone-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (= i (+ old-state-left.h 1)))
        (= return-left.value return-right.value)
    )
)
; i = h + 2
(define-lemma <relation-case-i-is-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (= i (+ 2 state-left.h)))
        (and
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 (+ 1 i) j)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 (+ 1 i) j)) (select state-right.LayeredKeys.WireKey (mk-tuple2 (+ 1 i) j)))
            (=>
                (< state-left.h 0)
                (and
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i l)))
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i r)))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i l)))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i r)))
                )
            )
            (=>
                (>= state-left.h 0)
                (and
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.KeysBot.ActiveBit l))
                    (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.KeysBot.ActiveBit r))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.KeysBot.WireKey l))
                    (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.KeysBot.WireKey r))
                )
            )
        )
    )
)

(define-lemma <relation-case-i-is-hplustwo-negative-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (= i (+ old-state-left.h 2))
             (< old-state-left.h 0))
        (= return-left.value return-right.value)
    )
)

(define-lemma <relation-case-i-is-hplustwo-nonnegative-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (= i (+ old-state-left.h 2))
             (>= old-state-left.h 0))
        (= return-left.value return-right.value)
    )
)
; i > h + 2
(define-lemma <relation-case-i-gt-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GarbleGate>
    (
        state-left
        state-right
        return-left
        return-right
        (i Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int)
    )
    (=>
        (and (> state-left.d 0) (>= i 1) (< i state-left.d)
             (> i (+ 2 state-left.h)))
        (and
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 (+ 1 i) j)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i l)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i r)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i r)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 (+ 1 i) j)) (select state-right.LayeredKeys.WireKey (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i l)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i l)))
            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i r)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i r)))
        )
    )
)

(define-lemma <relation-case-i-gt-hplustwo-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
        (and (> old-state-left.d 0) (>= i 1) (< i old-state-left.d)
             (> i (+ 2 old-state-left.h)))
        (= return-left.value return-right.value)
    )

)

(define-lemma <relation-assume-all-invariant-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
    (invariant old-state-left old-state-right)
)

(define-lemma <relation-assert-all-invariant-Hybrid$true$-Hybrid$false$+-GarbleGate>
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
    (invariant return-left.state return-right.state)
)
