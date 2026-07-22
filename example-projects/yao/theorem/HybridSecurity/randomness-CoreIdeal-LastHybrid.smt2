(define-fun randomness-mapping-GETAOUT
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
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (> d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and
                (= d 1)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
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
    (let 
        (
            (d (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
        )
        (or
            ; map Sim to LayeredSim for i < d
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rin_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
                (= sample-id-right (sample-id "LayeredSim" "LSIMGBLG" "rout_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Sim to Sim for i = d 
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_0"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_0"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_0"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_1"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_1"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_1"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_2"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_2"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_2"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rin_round_3"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rin_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Sim" "LSIMGBLG" "rout_round_3"))
                (= sample-id-right (sample-id "Sim" "GBLG" "rout_round_3"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to LayeredKeys for i < d - 1
            (and 
                (< <arg-CoreIdeal-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "r"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (< <arg-CoreIdeal-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "SimulatedLayersKeys" "LGETAOUT" "rr"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to TopKeys for i = d - 1
            (and 
                (= <arg-CoreIdeal-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "r"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> (- d 1))
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysTop" "GETAOUT" "rr"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            ; map Keys to BotKeys for i = d
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "r"))
                (= sample-id-right (sample-id "KeysBot" "GETAOUT" "r"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
            (and 
                (= <arg-CoreIdeal-GBLG-i> d)
                (= sample-id-left (sample-id "Keys" "LGETAOUT" "rr"))
                (= sample-id-right (sample-id "KeysBot" "GETAOUT" "rr"))
                (= sample-offset-left 0)
                (= sample-offset-right 0)
            )
        )
    )
)