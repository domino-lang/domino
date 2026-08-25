(define-randomness-mapping GETAOUT
    (left right consts)
    (or 
        (and 
            (= left.id (sample-id "Keys" "LGETAOUT" "r"))
            (= right.id (sample-id "KeysTop" "GETAOUT" "r"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
        (and 
            (= left.id (sample-id "Keys" "LGETAOUT" "rr"))
            (= right.id (sample-id "KeysTop" "GETAOUT" "rr"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
    )
)

(define-randomness-mapping GBLG
    (left right consts)
    (or
        (and
            (= left.args.i 1)
            (= left.id (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= right.id (sample-id "KeysBot" "GETKEYSOUT" "r"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
        (and
            (= left.args.i 1)
            (= left.id (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= right.id (sample-id "KeysBot" "GETKEYSOUT" "rr"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
        (and
            (= left.args.i 1)
            (= left.id (sample-id "Enc" "LENCN" "r"))
            (= right.id (sample-id "Enc" "ENCN" "r"))
            (= left.ctr right.ctr)
        )
        (and
            (= left.args.i 1)
            (= left.id (sample-id "Enc" "LENCM" "r"))
            (= right.id (sample-id "Enc" "ENCM" "r"))
            (= left.ctr right.ctr)
        )
        (and
            (> left.args.i 1)
            (= left.id (sample-id "Keys" "LGETKEYSOUT" "r"))
            (= right.id (sample-id "RealLayersKeys" "LGETKEYSOUT" "r"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
        (and
            (> left.args.i 1)
            (= left.id (sample-id "Keys" "LGETKEYSOUT" "rr"))
            (= right.id (sample-id "RealLayersKeys" "LGETKEYSOUT" "rr"))
            (= left.ctr 0)
            (= right.ctr 0)
        )
        (and
            (> left.args.i 1)
            (= left.id (sample-id "Enc" "LENCN" "r"))
            (= right.id (sample-id "LayeredEnc0" "LENCN" "r"))
            (= left.ctr right.ctr)
        )
        (and
            (> left.args.i 1)
            (= left.id (sample-id "Enc" "LENCM" "r"))
            (= right.id (sample-id "LayeredEnc0" "LENCM" "r"))
            (= left.ctr right.ctr)
        )
    )
)