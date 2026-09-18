(define-state-relation invariant
    (state-left state-right)
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i state-left.h)
                (and 
                    (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i j)))
                    (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i j)))
                )
            )
            (and
                ; ActiveBitSetAndGenerated / flag
                (= (select state-left.KeysTop.ActiveBitSetAndGenerated j) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.ActiveBitSetAndGenerated j) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
                (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
                ; WireKey / T
                (= (select state-left.KeysTop.WireKey j) (select state-right.SimulatedLayersKeys.T (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.WireKey j) (select state-right.KeysTop.WireKey j))
                (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.WireKey j))
                ; ActiveBit / z
                (= (select state-left.KeysTop.ActiveBit j) (select state-right.SimulatedLayersKeys.z (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.ActiveBit j) (select state-right.KeysTop.ActiveBit j))
                (= (select state-left.RealLayersKeys.z (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.ActiveBit j))
            )
            (=>
                (> i (+ state-left.h 2))
                (and
                    (= (select state-left.RealLayersKeys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.T (mk-tuple2 i j)) (select state-right.RealLayersKeys.T (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.z (mk-tuple2 i j)) (select state-right.RealLayersKeys.z (mk-tuple2 i j)))
                )
            )
        )
    )
)
