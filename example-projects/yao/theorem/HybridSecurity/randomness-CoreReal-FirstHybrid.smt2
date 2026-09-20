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
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "KeysTop" "GenerateWireKeys" "key_false"))
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
    (or
        (and
            (= <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (= <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "KeysBot" "GenerateWireKeys" "key_false"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (= <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Enc" "EncInner" "r"))
            (= sample-id-right (sample-id "Enc" "EncInner" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (= <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Enc" "EncOuter" "r"))
            (= sample-id-right (sample-id "Enc" "EncOuter" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (> <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_true"))
            (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_true"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Keys" "GenerateWireKeys" "key_false"))
            (= sample-id-right (sample-id "LayeredKeys" "GenerateWireKeys" "key_false"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Enc" "EncInner" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "EncInner" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (> <arg-CoreReal-GarbleGate-layer> 1)
            (= sample-id-left (sample-id "Enc" "EncOuter" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "EncOuter" "r"))
            (= sample-offset-left sample-offset-right)
        )
    )
)