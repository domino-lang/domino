(define-state-relation invariant
     (left-game right-game)
     (and
          (= left-game.keys_top.WireKey right-game.keys_top.WireKey)
          (= left-game.keys_top.ActiveBit right-game.keys_top.ActiveBit)
          (= left-game.keys_bottom.WireKey right-game.keys_bottom.WireKey)

          ; needed for GetOutputWireKeys
          (forall ((i Int))
               (=
                    (is-mk-none (select left-game.keys_bottom.ActiveBit i))
                    (is-mk-none (select right-game.keys_bottom.ActiveBit i))
               )
          )

          ; GarbleGate equal-aborts
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
          ; Alternatively we could say if WireKey[w] is not None, then for 
          ; both bits b, WireKey[w][b] is not none because the counterexample 
          ; comes from a case where ActiveBit is None and WireKey is not None 
          ; but the wire key for bit is not set.

          ; Another approach is to assert WireKey[wire] == None when setting the 
          ; active bit. Then we don't need this invariant and 2CPA can also be proved 
          ; as we still commit to active bit and then generate
     )
)
