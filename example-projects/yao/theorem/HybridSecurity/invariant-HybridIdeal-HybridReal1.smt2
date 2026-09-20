(define-state-relation invariant
    (state-left state-right)
    (let
        (
            (h state-left.h)
            (d state-left.d)
        )
        (and
            ; Outside the meaningful hybrid range both games use LayeredKeys.
            (=>
                (or (<= d 1) (< h 0) (>= h d))
                (forall
                    ((i Int) (j Int))
                    (and
                        (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                           (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                        (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                           (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                    )
                )
            )

            ; h = 0: CoreReal on the left and the first real layer on the
            ; right differ only by the KeysTop/KeysBot carve-out.
            (=>
                (and (> d 1) (= h 0))
                (and
                    (forall
                        ((j Int))
                        (and
                            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 1 j))
                               (select state-right.KeysTop.WireKey j))
                            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 1 j))
                               (select state-right.KeysTop.ActiveBit j))
                            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 2 j))
                               (select state-right.KeysBot.WireKey j))
                            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 2 j))
                               (select state-right.KeysBot.ActiveBit j))
                        )
                    )
                    (forall
                        ((i Int) (j Int))
                        (=>
                            (or (< i 1) (> i 2))
                            (and
                                (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                                (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                            )
                        )
                    )
                )
            )

            ; Interior hop: ideal layer h on the left and real layer h + 1 on
            ; the right overlap through both key packages.
            (=>
                (and (> h 0) (< h (- d 1)))
                (and
                    (forall
                        ((i Int) (j Int))
                        (=>
                            (< i h)
                            (and
                                (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                                (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                            )
                        )
                    )
                    (forall
                        ((j Int))
                        (and
                            (= (select state-left.KeysTop.WireKey j)
                               (select state-right.LayeredKeys.WireKey (mk-tuple2 h j)))
                            (= (select state-left.KeysTop.ActiveBit j)
                               (select state-right.LayeredKeys.ActiveBit (mk-tuple2 h j)))
                            (= (select state-left.KeysBot.WireKey j)
                               (select state-right.KeysTop.WireKey j))
                            (= (select state-left.KeysBot.ActiveBit j)
                               (select state-right.KeysTop.ActiveBit j))
                            (= (select state-left.LayeredKeys.WireKey (mk-tuple2 (+ h 2) j))
                               (select state-right.KeysBot.WireKey j))
                            (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 (+ h 2) j))
                               (select state-right.KeysBot.ActiveBit j))
                        )
                    )
                    (forall
                        ((i Int) (j Int))
                        (=>
                            (> i (+ h 2))
                            (and
                                (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                                (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                            )
                        )
                    )
                )
            )

            ; h = d - 1: the right game is the all-simulated endpoint h = d.
            (=>
                (and (> d 1) (= h (- d 1)))
                (and
                    (forall
                        ((i Int) (j Int))
                        (=>
                            (< i h)
                            (and
                                (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                                (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                            )
                        )
                    )
                    (forall
                        ((j Int))
                        (and
                            (= (select state-left.KeysTop.WireKey j)
                               (select state-right.LayeredKeys.WireKey (mk-tuple2 h j)))
                            (= (select state-left.KeysTop.ActiveBit j)
                               (select state-right.LayeredKeys.ActiveBit (mk-tuple2 h j)))
                            (= (select state-left.KeysBot.WireKey j)
                               (select state-right.LayeredKeys.WireKey (mk-tuple2 (+ h 1) j)))
                            (= (select state-left.KeysBot.ActiveBit j)
                               (select state-right.LayeredKeys.ActiveBit (mk-tuple2 (+ h 1) j)))
                        )
                    )
                    (forall
                        ((i Int) (j Int))
                        (=>
                            (> i (+ h 1))
                            (and
                                (= (select state-left.LayeredKeys.WireKey (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.WireKey (mk-tuple2 i j)))
                                (= (select state-left.LayeredKeys.ActiveBit (mk-tuple2 i j))
                                   (select state-right.LayeredKeys.ActiveBit (mk-tuple2 i j)))
                            )
                        )
                    )
                )
            )
        )
    )
)
