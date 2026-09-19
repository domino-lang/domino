;; TODO: this file still predates the LayeredKeys/Keys refactor.  It refers to
;; the package-state field `flag` and to `ActiveBitSetAndGenerated`, which no
;; longer exist, to the game instances `RealLayersKeys`/`SimulatedLayersKeys`,
;; which have been merged into a single `LayeredKeys`, and (in the randomness
;; mappings) to the eight coins `rin_round_*`/`rout_round_*` of the old
;; simulator, which now draws six (`rin_active`, `rout_active`, `rin_inactive`,
;; `rout_inactive`, `rout_zero_0`, `rout_zero_1`).  The names below have been
;; propagated mechanically; the statements themselves still need reworking.

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
                    (= (select state-left.SimulatedLayersKeys.WireKey (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.WireKey (mk-tuple2 i j)))
                    (= (select state-left.SimulatedLayersKeys.ActiveBit (mk-tuple2 i j)) (select state-right.SimulatedLayersKeys.ActiveBit (mk-tuple2 i j)))
                )
            )
            (and
                ; ActiveBitSetAndGenerated / flag
                (= (select state-left.KeysTop.ActiveBitSetAndGenerated j) (select state-right.SimulatedLayersKeys.flag (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.ActiveBitSetAndGenerated j) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
                (= (select state-left.RealLayersKeys.flag (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
                ; WireKey / T
                (= (select state-left.KeysTop.WireKey j) (select state-right.SimulatedLayersKeys.WireKey (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.WireKey j) (select state-right.KeysTop.WireKey j))
                (= (select state-left.RealLayersKeys.WireKey (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.WireKey j))
                ; ActiveBit / z
                (= (select state-left.KeysTop.ActiveBit j) (select state-right.SimulatedLayersKeys.ActiveBit (mk-tuple2 state-left.h j)))
                (= (select state-left.KeysBot.ActiveBit j) (select state-right.KeysTop.ActiveBit j))
                (= (select state-left.RealLayersKeys.ActiveBit (mk-tuple2 (+ state-left.h 2) j)) (select state-right.KeysBot.ActiveBit j))
            )
            (=>
                (> i (+ state-left.h 2))
                (and
                    (= (select state-left.RealLayersKeys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.WireKey (mk-tuple2 i j)) (select state-right.RealLayersKeys.WireKey (mk-tuple2 i j)))
                    (= (select state-left.RealLayersKeys.ActiveBit (mk-tuple2 i j)) (select state-right.RealLayersKeys.ActiveBit (mk-tuple2 i j)))
                )
            )
        )
    )
)
