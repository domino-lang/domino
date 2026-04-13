(define-state-relation invariants
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (forall 
        (
            (i Int)
            (j Int)
        )
        (and
            (=>
                (< i h)
                (and 
                    (= (select state-left.SimulatedLayersKeys.flag (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.SimulatedLayersKeys.T (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.T (mk-tuple2 i j)))
                    (= (select state-left.SimulatedLayersKeys.z (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.z (mk-tuple2 i j)))
                )
            )
            (and
                ; flag
                (= (select state-left.KeysTop.flag j) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 h j)))
                (= (select state-left.KeysBot.flag j) (select state-right.KeysTop.flag j))
                (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.flag j))
                ; T
                (= (select state-left.KeysTop.T j) (select state-right.SimulatedLayersKeys.T (mk-tuple2 h j)))
                (= (select state-left.KeysBot.T j) (select state-right.KeysTop.T j))
                (= (select state-left.RealLayersKeys.T (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.T j))
                ; z
                (= (select state-left.KeysTop.z j) (select state-right.SimulatedLayersKeys.z (mk-tuple2 h j)))
                (= (select state-left.KeysBot.z j) (select state-right.KeysTop.z j))
                (= (select state-left.RealLayersKeys.z (mk-tuple2 (+ h 2) j)) (select state-right.KeysBot.z j))
            )
            (=>
                (> i (+ h 2))
                (and
                    (= (select state-left.RealLayersKeys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.T (mk-tuple2 i j)) (select state-right.RealLayersKeys.T (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.z (mk-tuple2 i j)) (select state-right.RealLayersKeys.z (mk-tuple2 i j)))
                )
            )
        )
    )
)

(define-state-relation invariant
    (
        (state-left <GameState_HybridIdeal_<$<!n!><!m!><!p!><!w!><!d!><!h!>$>>)
        (state-right <GameState_HybridReal_<$<!n!><!m!><!p!><!w!><!d!><!hplusone!>$>>)
    )
    (invariants state-left state-right)
)