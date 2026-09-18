(define-state-relation invariant
    (state-left state-right)
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (= i 1)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBit j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.WireKey j))
                )
            )
            (=>
                (= i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBit j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.WireKey j))
                )
            )
            (=>
                (> i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.RealLayersKeys.z (mk-tuple2 i j)))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.RealLayersKeys.T (mk-tuple2 i j)))
                )
            )
        )
    )
)
