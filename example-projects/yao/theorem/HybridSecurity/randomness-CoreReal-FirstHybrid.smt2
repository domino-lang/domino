(define-fun randomness-mapping-GETAOUT
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (or 
        (and 
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and 
            (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
            (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
    )
)

(define-fun randomness-mapping-GBLG
    (
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-offset-left Int)
        (sample-offset-right Int)
    )
    Bool
    (or
        (and
            (= <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "r"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (= <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "KeysBot" "GETKEYSOUT" "rr"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (= <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCN" "r"))
            (= sample-id-right (sample-id "Enc" "ENCN" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (= <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCM" "r"))
            (= sample-id-right (sample-id "Enc" "ENCM" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (> <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= sample-id-right (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
            (= sample-offset-left 0)
            (= sample-offset-right 0)
        )
        (and
            (> <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCN" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCN" "r"))
            (= sample-offset-left sample-offset-right)
        )
        (and
            (> <arg-CoreReal-GBLG-i> 1)
            (= sample-id-left (sample-id "Enc" "LENCM" "r"))
            (= sample-id-right (sample-id "LayeredEnc0" "LENCM" "r"))
            (= sample-offset-left sample-offset-right)
        )
    )
)