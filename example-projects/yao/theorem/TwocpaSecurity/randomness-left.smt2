(define-fun randomness-mapping-GenerateInputWireKeys
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-GenerateInputWireKeys-wire>))))
      (and (= offset-0 0) (= offset-1 0)
        (ite active
          (or
            (and (= id-0 (sample-id "keys_top" "GenerateWireKeys" "key_true"))
                 (= id-1 (sample-id "reduction" "GenerateWireKeys" "active_key")))
            (and (= id-0 (sample-id "keys_top" "GenerateWireKeys" "key_false"))
                 (= id-1 (sample-id "cpa" "SampleKey" "key"))))
          (or
            (and (= id-0 (sample-id "keys_top" "GenerateWireKeys" "key_true"))
                 (= id-1 (sample-id "cpa" "SampleKey" "key")))
            (and (= id-0 (sample-id "keys_top" "GenerateWireKeys" "key_false"))
                 (= id-1 (sample-id "reduction" "GenerateWireKeys" "active_key")))))))))

(define-fun randomness-mapping-EncInner
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-EncInner-wire>))))
      (and (= id-0 (sample-id "enc" "EncInner" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-Twocpa0-EncInner-bit> active)
             (= id-1 (sample-id "reduction" "EncInner" "r"))
             (= id-1 (sample-id "cpa" "EncInner" "r")))))))

(define-fun randomness-mapping-EncOuter
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-EncOuter-wire>))))
      (and (= id-0 (sample-id "enc" "EncOuter" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-Twocpa0-EncOuter-bit> active)
             (= id-1 (sample-id "reduction" "EncOuter" "r"))
             (= id-1 (sample-id "cpa" "EncOuter" "r")))))))
