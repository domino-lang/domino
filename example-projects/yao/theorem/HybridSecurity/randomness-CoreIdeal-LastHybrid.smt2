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
                (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))
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
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_active"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_active"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_active"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_active"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_inactive"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_inactive"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_inactive"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_inactive"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_zero_0"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_zero_1"))
                (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_zero_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Sim to Sim for i = d 
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_active"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_active"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_active"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_active"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_inactive"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rin_inactive"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_inactive"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_inactive"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_zero_0"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_zero_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GarbleGate-layer> d)
                (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_zero_1"))
                (= sample-id-right (sample-id "Sim" "SimulateGarbledGate" "rout_zero_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to LayeredKeys for i < d - 1
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
                (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GarbleGate-layer> (- d 1))
                (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
                (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))
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
