(define-state-relation invariant
    (state-left state-right)
    (let 
        (
            (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
        )
        (forall 
            (
                (i Int)
                (j Int)
            )
            (and
                (=>
                    (< i d)
                    (and 
                        (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i j)))
                        (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i j)))
                        (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i j)))
                    )
                )
                (=>
                    (= i d)
                    (and 
                        (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
                        (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.WireKey j))
                        (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBit j))
                    )
                )
                (=>
                    (= i (+ d 1))
                    (and 
                        (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
                        (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.WireKey j))
                        (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBit j))
                    )
                )
            )
        )
    )
)
