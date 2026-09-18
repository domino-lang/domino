(define-state-relation invariant
     (left-game right-game)
     (and
          (= left-game.keys_top.WireKey right-game.keys_top.WireKey)
          (= left-game.keys_top.ActiveBit right-game.keys_top.ActiveBit)
          (= left-game.keys_top.ActiveBitSetAndGenerated right-game.keys_top.ActiveBitSetAndGenerated)
          (= left-game.keys_bottom.WireKey right-game.keys_bottom.WireKey)
          (= left-game.keys_bottom.ActiveBitSetAndGenerated right-game.keys_bottom.ActiveBitSetAndGenerated)

          (forall ((i Int)) 
               (= 
                    (is-mk-none (select right-game.keys_bottom.ActiveBit i)) 
                    (not (= (mk-some true) (select left-game.keys_bottom.ActiveBitSetAndGenerated i)))
               )
          )

          (forall ((i Int) (b Bool))
               (=> 
                    (not (is-mk-none (select left-game.keys_bottom.WireKey i)))
                    (not (is-mk-none (select (maybe-get (select left-game.keys_bottom.WireKey i)) b)))
               )
          )
     )
)
