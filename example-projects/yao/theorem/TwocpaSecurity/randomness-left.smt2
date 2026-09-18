(define-fun randomness-mapping-GETAOUT
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-GETAOUT-h>))))
      (and (= offset-0 0) (= offset-1 0)
        (ite active
          (or
            (and (= id-0 (sample-id "keys_top" "GETAOUT" "r"))
                 (= id-1 (sample-id "reduction" "GETAOUT" "active_key")))
            (and (= id-0 (sample-id "keys_top" "GETAOUT" "rr"))
                 (= id-1 (sample-id "cpa" "SAMPLEKEY" "key"))))
          (or
            (and (= id-0 (sample-id "keys_top" "GETAOUT" "r"))
                 (= id-1 (sample-id "cpa" "SAMPLEKEY" "key")))
            (and (= id-0 (sample-id "keys_top" "GETAOUT" "rr"))
                 (= id-1 (sample-id "reduction" "GETAOUT" "active_key")))))))))

(define-fun randomness-mapping-ENCN
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-ENCN-j>))))
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-Twocpa0-ENCN-b> active)
             (= id-1 (sample-id "reduction" "ENCN" "r"))
             (= id-1 (sample-id "cpa" "ENCN" "r")))))))

(define-fun randomness-mapping-ENCM
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((keys-top
          (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-Twocpa0-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)
                <arg-Twocpa0-ENCM-j>))))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-Twocpa0-ENCM-b> active)
             (= id-1 (sample-id "reduction" "ENCM" "r"))
             (= id-1 (sample-id "cpa" "ENCM" "r")))))))
