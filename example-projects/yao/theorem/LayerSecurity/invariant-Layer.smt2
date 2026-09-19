(define-state-relation invariant
     (left-game right-game)
     (and
          (= left-game.keys_top.WireKey right-game.keys_top.WireKey)
          (= left-game.keys_top.ActiveBit right-game.keys_top.ActiveBit)
          (= left-game.keys_bottom.WireKey right-game.keys_bottom.WireKey)

          (forall ((i Int))
               (=
                    (is-mk-none (select left-game.keys_bottom.ActiveBit i))
                    (is-mk-none (select right-game.keys_bottom.ActiveBit i))
               )
          )

          ;; GenerateWireKeys refuses to run before SetActiveBit, so a wire that
          ;; has keys also has an active bit.  Needed for GarbleGate's aborts:
          ;; a wire whose keys already exist makes both SetInputBit (left) and
          ;; Eval's SetActiveBit (right) abort, which is what keeps Gate's
          ;; Unwrap(Z[bj]) -- it reads *both* entries of the table -- in step
          ;; with the simulator, which only ever reads the active one.
          (forall ((i Int))
               (=>
                    (not (is-mk-none (select left-game.keys_bottom.WireKey i)))
                    (not (is-mk-none (select left-game.keys_bottom.ActiveBit i)))
               )
          )
     )
)
