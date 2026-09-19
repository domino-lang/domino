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
    (or
        (and
            (= (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>) 1)
            (= sample-id-left (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (= (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>) 1)
            (= sample-id-left (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>) 1)
            (= sample-id-left (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>) 1)
            (= sample-id-left (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
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
  (let ((h (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>)))
    (or
        (and 
            (< <arg-HybridIdeal-GarbleGate-layer> (- h 1))
            (or 
                (= sample-id-left sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
                (= sample-id-left sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_3"))
            )
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (- h 1))
            (= sample-id-left (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (- h 1))
            (= sample-id-left (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "SimulatedLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (- h 1))
            (or
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_3"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_0"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_1"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_2"))
                (= sample-id-left sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_3"))
            )
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_0"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_0"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_0"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_1"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_1"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_1"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_2"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_2"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_2"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rin_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rin_round_3"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> h)
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "Sim" "SimulateGarbledGate" "rout_round_3"))
            (= sample-id-right (sample-id "LayeredSim" "SimulateGarbledGate" "rout_round_3"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "RealLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "RealLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left sample-offset-right)
            (= sample-id-left (sample-id "LayeredEnc0" "EncInner" "r"))
            (= sample-id-right (sample-id "Enc" "EncInner" "r"))
        )
        (and 
            (= <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left sample-offset-right)
            (= sample-id-left (sample-id "LayeredEnc0" "EncOuter" "r"))
            (= sample-id-right (sample-id "Enc" "EncOuter" "r"))
        )
        (and 
            (> <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "RealLayersKeys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "RealLayersKeys" "GenerateWireKeys" "key_true"))
        )
        (and 
            (> <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
            (= sample-id-left (sample-id "RealLayersKeys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "RealLayersKeys" "GenerateWireKeys" "key_false"))
        )
        (and 
            (> <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left sample-offset-right)
            (= sample-id-left (sample-id "LayeredEnc0" "EncInner" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "EncInner" "r"))
        )
        (and 
            (> <arg-HybridIdeal-GarbleGate-layer> (+ h 1))
            (= sample-offset-left sample-offset-right)
            (= sample-id-left (sample-id "LayeredEnc0" "EncOuter" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "EncOuter" "r"))
        )
        )
    )
)
