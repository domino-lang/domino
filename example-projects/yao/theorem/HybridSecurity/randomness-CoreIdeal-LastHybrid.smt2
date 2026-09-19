;; TODO: this file still predates the LayeredKeys/Keys refactor.  It refers to
;; the package-state field `flag` and to `ActiveBitSetAndGenerated`, which no
;; longer exist, to the game instances `RealLayersKeys`/`SimulatedLayersKeys`,
;; which have been merged into a single `LayeredKeys`, and (in the randomness
;; mappings) to the eight coins `rin_round_*`/`rout_round_*` of the old
;; simulator, which now draws six (`rin_active`, `rout_active`, `rin_inactive`,
;; `rout_inactive`, `rout_zero_0`, `rout_zero_1`).  The names below have been
;; propagated mechanically; the statements themselves still need reworking.

(define-fun randomness-mapping-GenerateInputWireKeys
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (let 
        (
            (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
        )
        (or 
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
        )
    )
)

(define-fun randomness-mapping-GarbleGate
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (let 
        (
            (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
        )
        (or
            ; map Sim to LayeredSim for i < d
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Sim to Sim for i = d 
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_3"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to LayeredKeys for i < d - 1
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to TopKeys for i = d - 1
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to BotKeys for i = d
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
        )
    )
)