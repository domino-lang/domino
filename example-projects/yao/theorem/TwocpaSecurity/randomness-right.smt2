(define-fun randomness-mapping-GenerateInputWireKeys
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaReduction-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaReduction1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaReduction-GenerateInputWireKeys-wire>))))
      (and (= offset-0 0) (= offset-1 0)
        (ite active
          (or
            (and (= id-0 (sample-id "reduction" "GenerateWireKeys" "active_key"))
                 (= id-1 (sample-id "keys_top" "GenerateWireKeys" "key_true")))
            (and (= id-0 (sample-id "cpa" "SampleKey" "key"))
                 (= id-1 (sample-id "keys_top" "GenerateWireKeys" "key_false"))))
          (or
            (and (= id-0 (sample-id "cpa" "SampleKey" "key"))
                 (= id-1 (sample-id "keys_top" "GenerateWireKeys" "key_true")))
            (and (= id-0 (sample-id "reduction" "GenerateWireKeys" "active_key"))
                 (= id-1 (sample-id "keys_top" "GenerateWireKeys" "key_false")))))))))

(define-fun randomness-mapping-EncInner
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaReduction-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaReduction1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaReduction-EncInner-wire>))))
      (and (= id-1 (sample-id "enc" "EncInner" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-TwocpaReduction-EncInner-bit> active)
             (= id-0 (sample-id "reduction" "EncInner" "r"))
             (= id-0 (sample-id "cpa" "EncInner" "r")))))))

(define-fun randomness-mapping-EncOuter
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaReduction-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaReduction1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaReduction-EncOuter-wire>))))
      (and (= id-1 (sample-id "enc" "EncOuter" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-TwocpaReduction-EncOuter-bit> active)
             (= id-0 (sample-id "reduction" "EncOuter" "r"))
             (= id-0 (sample-id "cpa" "EncOuter" "r")))))))
