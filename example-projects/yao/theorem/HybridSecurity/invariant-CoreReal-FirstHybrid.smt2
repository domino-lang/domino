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
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBit j))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.KeysTop.WireKey j))
                )
            )
            (=>
                (= i 2)
                (and 
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBit j))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.KeysBot.WireKey j))
                )
            )
            (=>
                (> i 2)
                (and 
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                )
            )
        )
    )
)
