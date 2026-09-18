(define-fun randomness-mapping-GETAOUT
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaViaCpa1-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaViaCpa1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaViaCpa1-GETAOUT-h>))))
      (and (= offset-0 0) (= offset-1 0)
        (ite active
          (or
            (and (= id-0 (sample-id "reduction" "GETAOUT" "active_key"))
                 (= id-1 (sample-id "keys_top" "GETAOUT" "r")))
            (and (= id-0 (sample-id "cpa" "SAMPLEKEY" "key"))
                 (= id-1 (sample-id "keys_top" "GETAOUT" "rr"))))
          (or
            (and (= id-0 (sample-id "cpa" "SAMPLEKEY" "key"))
                 (= id-1 (sample-id "keys_top" "GETAOUT" "r")))
            (and (= id-0 (sample-id "reduction" "GETAOUT" "active_key"))
                 (= id-1 (sample-id "keys_top" "GETAOUT" "rr")))))))))

(define-fun randomness-mapping-ENCN
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaViaCpa1-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaViaCpa1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaViaCpa1-ENCN-h>))))
      (and (= id-1 (sample-id "enc" "ENCN" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-TwocpaViaCpa1-ENCN-d> active)
             (= id-0 (sample-id "reduction" "ENCN" "r"))
             (= id-0 (sample-id "cpa" "ENCN" "r")))))))

(define-fun randomness-mapping-ENCM
  ((id-0 SampleId) (id-1 SampleId) (offset-0 Int) (offset-1 Int))
  Bool
  (let ((reduction
          (<game-TwocpaViaCpa1-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
            <<game-state-TwocpaViaCpa1-old>>)))
    (let ((active
            (maybe-get
              (select
                (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit> reduction)
                <arg-TwocpaViaCpa1-ENCM-h>))))
      (and (= id-1 (sample-id "enc" "ENCM" "r"))
           (= offset-0 0) (= offset-1 0)
           (ite (= <arg-TwocpaViaCpa1-ENCM-d> active)
             (= id-0 (sample-id "reduction" "ENCM" "r"))
             (= id-0 (sample-id "cpa" "ENCM" "r")))))))
