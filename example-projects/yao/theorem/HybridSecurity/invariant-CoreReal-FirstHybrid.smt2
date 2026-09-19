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
                (= i 1)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBitSetAndGenerated j))
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.KeysTop.ActiveBit j))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.KeysTop.WireKey j))
                )
            )
            (=>
                (= i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBitSetAndGenerated j))
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.KeysBot.ActiveBit j))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.KeysBot.WireKey j))
                )
            )
            (=>
                (> i 2)
                (and 
                    (= (select state-left.Keys.flag (mk-tuple2 i j)) (select state-right.RealLayersKeys.flag (mk-tuple2 i j)))
                    (= (select state-left.Keys.ActiveBit (mk-tuple2 i j)) (select state-right.RealLayersKeys.ActiveBit (mk-tuple2 i j)))
                    (= (select state-left.Keys.WireKey (mk-tuple2 i j)) (select state-right.RealLayersKeys.WireKey (mk-tuple2 i j)))
                )
            )
        )
    )
)
