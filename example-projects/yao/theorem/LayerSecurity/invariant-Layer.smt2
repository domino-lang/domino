(define-state-relation invariant
     (left-game right-game)
     (and
          (= left-game.keys_top.T right-game.keys_top.T)
          (= left-game.keys_top.z right-game.keys_top.z)
          (= left-game.keys_top.flag right-game.keys_top.flag)
          (= left-game.keys_bottom.T right-game.keys_bottom.T)
          (= left-game.keys_bottom.flag right-game.keys_bottom.flag)


          (forall ((i Int)) 
               (= 
                    (is-mk-none (select right-game.keys_bottom.z i)) 
                    (not (= (mk-some true) (select left-game.keys_bottom.flag i)))
               )
          )
     )
)
