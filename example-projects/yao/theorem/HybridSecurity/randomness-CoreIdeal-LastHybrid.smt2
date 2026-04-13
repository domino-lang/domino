(define-fun randomness-mapping-GETAOUT
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    (let 
        (
            (d (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>))
        )
        (or 
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
        )
    )
)

(define-fun randomness-mapping-SETBIT
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    false
)

(define-fun randomness-mapping-GBLG
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    (let 
        (
            (d (<theorem-consts-HybridCircuitSecurity-d> <<theorem-consts>>))
        )
        (or
            ; map Sim to LayeredSim for i < d
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_0"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_0"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_1"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_1"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_2"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_2"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_3"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_3"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            ; map Sim to Sim for i = d 
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_0"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_0"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_1"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_1"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_2"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_2"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_3"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_3"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            ; map Keys to LayeredKeys for i < d - 1
            (and 
                (< <arg-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (< <arg-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            ; map Keys to TopKeys for i = d - 1
            (and 
                (= <arg-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            ; map Keys to BotKeys for i = d
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysBot" "GETAOUT" "r"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
            (and 
                (= <arg-GBLG-i> d)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysBot" "GETAOUT" "rr"))
                (= sample-ctr-left sample-ctr-old-left)
                (= sample-ctr-right sample-ctr-old-right)
            )
        )
    )
)

(define-fun randomness-mapping-GETKEYSIN
    (
        (sample-ctr-old-left Int)
        (sample-ctr-old-right Int)
        (sample-id-left SampleId)
        (sample-id-right SampleId)
        (sample-ctr-left Int)
        (sample-ctr-right Int)
    )
    Bool
    false
)