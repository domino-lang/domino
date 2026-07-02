(define-state-relation invariant
     (
          (left-game <GameState_LayerHybrid_<$<!n!><!m!><!p!>$>>)
          (right-game <GameState_LayerIdeal_<$<!n!><!m!><!p!>$>>)
     )
     (and
          (= left-game.keys_top.T right-game.keys_top.T)
          (= left-game.keys_top.z right-game.keys_top.z)
          (= left-game.keys_top.flag right-game.keys_top.flag)
          (= left-game.keys_bottom.T right-game.keys_bottom.T)
          (= left-game.keys_bottom.flag right-game.keys_bottom.flag)

     )
)