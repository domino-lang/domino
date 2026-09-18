(define-state-relation invariant
  (left-game right-game)
  (and
    (= left-game.reduction.ActiveBit
       right-game.keys_top.ActiveBit)
    (= left-game.reduction.Initialized
       right-game.keys_top.ActiveBitSetAndGenerated)
    (forall ((h Int))
      (let ((initialized (select left-game.reduction.Initialized h)))
        (and
          (or (is-mk-none initialized) (= initialized (mk-some true)))
          (= (is-mk-none initialized)
             (is-mk-none (select right-game.keys_top.WireKey h)))
          (= (is-mk-none initialized)
             (is-mk-none (select left-game.reduction.ActiveKey h)))
          (= (is-mk-none initialized)
             (is-mk-none (select left-game.cpa.Key h)))
          (=>
            (= initialized (mk-some true))
            (and
              (not (is-mk-none (select left-game.reduction.ActiveBit h)))
              (let ((a (maybe-get (select left-game.reduction.ActiveBit h)))
                    (wire-keys (maybe-get (select right-game.keys_top.WireKey h))))
                (and
                  (not (is-mk-none (select wire-keys a)))
                  (not (is-mk-none (select wire-keys (not a))))
                  (= (maybe-get (select left-game.reduction.ActiveKey h))
                     (maybe-get (select wire-keys a)))
                  (= (maybe-get (select left-game.cpa.Key h))
                     (maybe-get (select wire-keys (not a)))))))))))))

(define-fun randomness-mapping-GETAOUT
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit>
                (<game-TwocpaViaMultiCpaRight-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
                  <<game-state-ViaRight-old>>))
              <arg-TwocpaViaMultiCpaRight-GETAOUT-h>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (or
        (and a
             (= id-0 (sample-id "reduction" "GETAOUT" "k"))
             (= id-1 (sample-id "keys_top" "GETAOUT" "r")))
        (and a
             (= id-0 (sample-id "cpa" "SAMPLEKEY" "k"))
             (= id-1 (sample-id "keys_top" "GETAOUT" "rr")))
        (and (not a)
             (= id-0 (sample-id "reduction" "GETAOUT" "k"))
             (= id-1 (sample-id "keys_top" "GETAOUT" "rr")))
        (and (not a)
             (= id-0 (sample-id "cpa" "SAMPLEKEY" "k"))
             (= id-1 (sample-id "keys_top" "GETAOUT" "r")))))))

(define-fun randomness-mapping-ENCN
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit>
                (<game-TwocpaViaMultiCpaRight-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
                  <<game-state-ViaRight-old>>))
              <arg-TwocpaViaMultiCpaRight-ENCN-h>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (= id-1 (sample-id "enc" "ENCN" "r"))
      (ite
        (= <arg-TwocpaViaMultiCpaRight-ENCN-d> a)
        (= id-0 (sample-id "reduction" "ENCN" "r"))
        (= id-0 (sample-id "cpa" "ENCN" "r"))))))

(define-fun randomness-mapping-ENCM
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-TwocpaReduction-<$<!m!><!n!><!p!>$>-ActiveBit>
                (<game-TwocpaViaMultiCpaRight-<$<!n!><!m!><!p!>$>-pkgstate-reduction>
                  <<game-state-ViaRight-old>>))
              <arg-TwocpaViaMultiCpaRight-ENCM-h>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (= id-1 (sample-id "enc" "ENCM" "r"))
      (ite
        (= <arg-TwocpaViaMultiCpaRight-ENCM-d> a)
        (= id-0 (sample-id "reduction" "ENCM" "r"))
        (= id-0 (sample-id "cpa" "ENCM" "r"))))))
