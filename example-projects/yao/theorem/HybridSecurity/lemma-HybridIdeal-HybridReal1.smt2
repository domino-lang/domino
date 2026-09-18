(define-lemma <relation-value-of-h-Hybrid$true$-Hybrid$false$+-SETBIT>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (j Int)
        (b Bool)
    )
    (= old-state-left.h -2)
)


(define-lemma <relation-value-of-h-Hybrid$true$-Hybrid$false$+-GETKEYSIN>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (j Int)
    )
    (= old-state-left.h 1)
)

(define-lemma <relation-value-of-h-Hybrid$true$-Hybrid$false$+-GETAOUT>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (j Int)
    )
    (= old-state-left.h 1)
)

(define-lemma <relation-value-of-i-Hybrid$true$-Hybrid$false$+-GBLG>
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
    (= i (+ old-state-left.h 1))
)

(define-lemma <relation-inv-case-i-lt-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (< i (- old-state-left.h 1))
        (and
            (= return-left.state.RealLayersKeys.flag old-state-left.RealLayersKeys.flag)
            (= return-left.state.KeysTop.ActiveBitSetAndGenerated old-state-left.KeysTop.ActiveBitSetAndGenerated)
            (= return-left.state.KeysBot.ActiveBitSetAndGenerated old-state-left.KeysBot.ActiveBitSetAndGenerated)
            (= return-right.state.RealLayersKeys.flag old-state-right.RealLayersKeys.flag)
            (= return-right.state.KeysTop.ActiveBitSetAndGenerated old-state-right.KeysTop.ActiveBitSetAndGenerated)
            (= return-right.state.KeysBot.ActiveBitSetAndGenerated old-state-right.KeysBot.ActiveBitSetAndGenerated)
            (= return-left.state.RealLayersKeys.T old-state-left.RealLayersKeys.T)
            (= return-left.state.KeysTop.WireKey old-state-left.KeysTop.WireKey)
            (= return-left.state.KeysBot.WireKey old-state-left.KeysBot.WireKey)
            (= return-right.state.RealLayersKeys.T old-state-right.RealLayersKeys.T)
            (= return-right.state.KeysTop.WireKey old-state-right.KeysTop.WireKey)
            (= return-right.state.KeysBot.WireKey old-state-right.KeysBot.WireKey)
            (= return-left.state.RealLayersKeys.z old-state-left.RealLayersKeys.z)
            (= return-left.state.KeysTop.ActiveBit old-state-left.KeysTop.ActiveBit)
            (= return-left.state.KeysBot.ActiveBit old-state-left.KeysBot.ActiveBit)
            (= return-right.state.RealLayersKeys.z old-state-right.RealLayersKeys.z)
            (= return-right.state.KeysTop.ActiveBit old-state-right.KeysTop.ActiveBit)
            (= return-right.state.KeysBot.ActiveBit old-state-right.KeysBot.ActiveBit)
        )
    )
)

(define-lemma <relation-inv-case-i-lt-hminusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (< i (- old-state-left.h 1))
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hminusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (- old-state-left.h 1))
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-h-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i old-state-left.h)
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ old-state-left.h 1))
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-is-hplustwo-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ old-state-left.h 2))
        (invariant return-left.state return-right.state)
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (> i (+ old-state-left.h 2))
        (let
            (
                (r return-right.state.RealLayersKeys.r)
                (rr return-right.state.RealLayersKeys.rr)
            )
            (and
                (= return-left.state.RealLayersKeys.flag (store old-state-left.RealLayersKeys.flag (mk-tuple2 (+ i 1) j) (mk-some true)))
                (= return-left.state.SimulatedLayersKeys.flag old-state-left.SimulatedLayersKeys.flag)
                (= return-left.state.KeysTop.ActiveBitSetAndGenerated old-state-left.KeysTop.ActiveBitSetAndGenerated)
                (= return-left.state.KeysBot.ActiveBitSetAndGenerated old-state-left.KeysBot.ActiveBitSetAndGenerated)
                (= return-right.state.RealLayersKeys.flag (store old-state-right.RealLayersKeys.flag (mk-tuple2 (+ i 1) j) (mk-some true)))
                (= return-right.state.SimulatedLayersKeys.flag old-state-right.SimulatedLayersKeys.flag)
                (= return-right.state.KeysTop.ActiveBitSetAndGenerated old-state-right.KeysTop.ActiveBitSetAndGenerated)
                (= return-right.state.KeysBot.ActiveBitSetAndGenerated old-state-right.KeysBot.ActiveBitSetAndGenerated)

                (=>
                    (not (is-mk-none (select old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j))))
                    (= return-left.state.RealLayersKeys.T old-state-left.RealLayersKeys.T)
                )
                (=>
                    (is-mk-none (select old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j)))
                    (= return-left.state.RealLayersKeys.T
                        (store old-state-left.RealLayersKeys.T (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        )
                    )
                )
                (= return-left.state.SimulatedLayersKeys.T old-state-left.SimulatedLayersKeys.T)
                (= return-left.state.KeysTop.WireKey old-state-left.KeysTop.WireKey)
                (= return-left.state.KeysBot.WireKey old-state-left.KeysBot.WireKey)

                (=>
                    (not (is-mk-none (select old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j))))
                    (= return-right.state.RealLayersKeys.T old-state-right.RealLayersKeys.T)
                )
                (=>
                    (is-mk-none (select old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j)))
                    (= return-right.state.RealLayersKeys.T
                        (store old-state-right.RealLayersKeys.T (mk-tuple2 (+ i 1) j)
                            (mk-some (store
                                (store
                                    ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n)))
                                    true
                                    (mk-some r)
                                )
                                false
                                (mk-some rr)
                            ))
                        )
                    )
                )
                (= return-right.state.SimulatedLayersKeys.T old-state-right.SimulatedLayersKeys.T)
                (= return-right.state.KeysTop.WireKey old-state-right.KeysTop.WireKey)
                (= return-right.state.KeysBot.WireKey old-state-right.KeysBot.WireKey)

                (= return-left.state.RealLayersKeys.z old-state-left.RealLayersKeys.z)
                (= return-left.state.SimulatedLayersKeys.z old-state-left.SimulatedLayersKeys.z)
                (= return-left.state.KeysTop.ActiveBit old-state-left.KeysTop.ActiveBit)
                (= return-left.state.KeysBot.ActiveBit old-state-left.KeysBot.ActiveBit)
                (= return-right.state.RealLayersKeys.z old-state-right.RealLayersKeys.z)
                (= return-right.state.SimulatedLayersKeys.z old-state-right.SimulatedLayersKeys.z)
                (= return-right.state.KeysTop.ActiveBit old-state-right.KeysTop.ActiveBit)
                (= return-right.state.KeysBot.ActiveBit old-state-right.KeysBot.ActiveBit)
            )
        )
    )
)

(define-lemma <relation-inv-case-i-gt-hplustwo-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (> i (+ old-state-left.h 2))
        (invariant return-left.state return-right.state)
    )
)

; i < h - 1
(define-lemma <relation-case-i-lt-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (< i (- state-left.h 1))
        (and
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 (+ i 1) j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 (+ i 1) j)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 (+ i 1) j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 (+ i 1) j)))
        )
    )
)

(define-lemma <relation-case-i-lt-hminusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (< i (- old-state-left.h 1))
        (= return-left.value return-right.value)
    )
)

; i = h - 1
(define-lemma <relation-case-i-is-hminusone-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (- state-left.h 1))
        (and
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i l)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i r)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i r)))
            (= (select state-left.KeysTop.ActiveBit j) (select state-right.SimulatedLayersKeys.z (mk-tuple2 state-left.h j)))
            (= (select state-left.KeysTop.WireKey j) (select state-right.SimulatedLayersKeys.T (mk-tuple2 state-left.h j)))
        )
    )
)

(define-lemma <relation-case-i-is-hminusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (- old-state-left.h 1))
        (= return-left.value return-right.value)
    )
)

; i = h
(define-lemma <relation-case-i-is-h-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i state-left.h)
        (and
            (= (select state-left.KeysTop.ActiveBit l) (select state-right.SimulatedLayersKeys.z (mk-tuple2 state-left.h l)))
            (= (select state-left.KeysTop.ActiveBit r) (select state-right.SimulatedLayersKeys.z (mk-tuple2 state-left.h r)))
            (= (select state-left.KeysTop.ActiveBitSetAndGenerated l) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 state-left.h l)))
            (= (select state-left.KeysTop.ActiveBitSetAndGenerated r) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 state-left.h r)))
            (= (select state-left.KeysTop.WireKey l) (select state-right.SimulatedLayersKeys.T (mk-tuple2 state-left.h l)))
            (= (select state-left.KeysTop.WireKey r) (select state-right.SimulatedLayersKeys.T (mk-tuple2 state-left.h r)))
            (= (select state-left.KeysBot.ActiveBit j) (select state-right.KeysTop.ActiveBit j))
            (= (select state-left.KeysBot.WireKey j) (select state-right.KeysTop.WireKey j))
            (= (select state-left.KeysBot.ActiveBitSetAndGenerated j) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
        )
    )
)

(define-lemma <relation-case-i-is-h-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i old-state-left.h)
        (= return-left.value return-right.value)
    )
)

; i = h + 1
(define-lemma <relation-case-i-is-hplusone-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ 1 state-left.h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 2 state-left.h) j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
            (= (select state-left.KeysBot.ActiveBitSetAndGenerated l) (select state-right.KeysTop.ActiveBitSetAndGenerated l))
            (= (select state-left.KeysBot.ActiveBitSetAndGenerated r) (select state-right.KeysTop.ActiveBitSetAndGenerated r))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 2 state-left.h) j)) (select state-right.KeysBot.WireKey j))
            (= (select state-left.KeysBot.WireKey l) (select state-right.KeysTop.WireKey l))
            (= (select state-left.KeysBot.WireKey r) (select state-right.KeysTop.WireKey r))
        )
    )
)

(define-lemma <relation-case-i-is-hplusone-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ old-state-left.h 1))
        (= return-left.value return-right.value)
    )
)
; i = h + 2
(define-lemma <relation-case-i-is-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ 2 state-left.h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i l)) (select state-right.KeysBot.ActiveBitSetAndGenerated l))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i r)) (select state-right.KeysBot.ActiveBitSetAndGenerated r))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i l)) (select state-right.KeysBot.WireKey l))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i r)) (select state-right.KeysBot.WireKey r))
        )
    )
)

(define-lemma <relation-case-i-is-hplustwo-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (= i (+ old-state-left.h 2))
        (= return-left.value return-right.value)
    )
)
; i > h + 2
(define-lemma <relation-case-i-gt-hplustwo-assumptions-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (> i (+ 2 state-left.h))
        (and
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.flag (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i l)) (select state-right.RealLayersKeys.flag (mk-tuple2 i l)))
            (= (select state-left.RealLayersKeys.flag (mk-tuple2 i r)) (select state-right.RealLayersKeys.flag (mk-tuple2 i r)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)) (select state-right.RealLayersKeys.T (mk-tuple2 (+ 1 i) j)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i l)) (select state-right.RealLayersKeys.T (mk-tuple2 i l)))
            (= (select state-left.RealLayersKeys.T (mk-tuple2 i r)) (select state-right.RealLayersKeys.T (mk-tuple2 i r)))
        )
    )
)

(define-lemma <relation-case-i-gt-hplustwo-Hybrid$true$-Hybrid$false$+-GBLG>
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
        (> i (+ 2 old-state-left.h))
        (= return-left.value return-right.value)
    )

)

(define-lemma <relation-assume-all-invariant-Hybrid$true$-Hybrid$false$+-GBLG>
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

(define-lemma <relation-assert-all-invariant-Hybrid$true$-Hybrid$false$+-GBLG>
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
