(define-state-relation invariant
    (
        (state-left <GameState_CoreReal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!1!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (= i 1)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.flag j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.z j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.T j))
                )
            )
            (=>
                (= i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.flag j))
                    (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.z j))
                    (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.T j))
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