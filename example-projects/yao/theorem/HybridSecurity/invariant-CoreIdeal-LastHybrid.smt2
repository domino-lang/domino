(define-state-relation invariant
    (
        (state-left <GameState_CoreIdeal_<$<!n!><!m!><!p!><!w!><!d!>$>>)
        (state-right <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!d!>$>>)
    )
    (let 
        (
            (d (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>))
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
                        (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.flag j))
                        (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysTop.T j))
                        (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysTop.z j))
                    )
                )
                (=>
                    (= i (+ d 1))
                    (and 
                        (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.flag j))
                        (= (select state-left.Keys.T (mk-tuple2 i j)) (select state-right.KeysBot.T j))
                        (= (select state-left.Keys.z (mk-tuple2 i j)) (select state-right.KeysBot.z j))
                    )
                )
            )
        )
    )
)