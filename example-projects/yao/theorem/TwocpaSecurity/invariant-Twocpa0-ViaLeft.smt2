(define-state-relation invariant
  (left-game right-game)
  (and
    (= left-game.keys_top.ActiveBit
       right-game.reduction.ActiveBit)
    (= left-game.keys_top.ActiveBitSetAndGenerated
       right-game.reduction.Initialized)
    (forall ((h Int))
      (let ((initialized (select right-game.reduction.Initialized h)))
        (and
          (or (is-mk-none initialized) (= initialized (mk-some true)))
          (= (is-mk-none initialized)
             (is-mk-none (select left-game.keys_top.WireKey h)))
          (= (is-mk-none initialized)
             (is-mk-none (select right-game.reduction.ActiveKey h)))
          (= (is-mk-none initialized)
             (is-mk-none (select right-game.cpa.Key h)))
          (=>
            (= initialized (mk-some true))
            (and
              (not (is-mk-none (select right-game.reduction.ActiveBit h)))
              (let ((a (maybe-get (select right-game.reduction.ActiveBit h)))
                    (wire-keys (maybe-get (select left-game.keys_top.WireKey h))))
                (and
                  (not (is-mk-none (select wire-keys a)))
                  (not (is-mk-none (select wire-keys (not a))))
                  (= (maybe-get (select wire-keys a))
                     (maybe-get (select right-game.reduction.ActiveKey h)))
                  (= (maybe-get (select wire-keys (not a)))
                     (maybe-get (select right-game.cpa.Key h))))))))))))

(define-fun randomness-mapping-GETAOUT
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-Keys-<$<!n!>$>-ActiveBit>
                (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
                  <<game-state-Twocpa0-old>>))
              <arg-Twocpa0-GETAOUT-h>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (or
        (and a
             (= id-0 (sample-id "keys_top" "GETAOUT" "r"))
             (= id-1 (sample-id "reduction" "GETAOUT" "k")))
        (and a
             (= id-0 (sample-id "keys_top" "GETAOUT" "rr"))
             (= id-1 (sample-id "cpa" "SAMPLEKEY" "k")))
        (and (not a)
             (= id-0 (sample-id "keys_top" "GETAOUT" "rr"))
             (= id-1 (sample-id "reduction" "GETAOUT" "k")))
        (and (not a)
             (= id-0 (sample-id "keys_top" "GETAOUT" "r"))
             (= id-1 (sample-id "cpa" "SAMPLEKEY" "k")))))))

(define-fun randomness-mapping-ENCN
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-Keys-<$<!n!>$>-ActiveBit>
                (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
                  <<game-state-Twocpa0-old>>))
              <arg-Twocpa0-ENCN-j>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (= id-0 (sample-id "enc" "ENCN" "r"))
      (ite
        (= <arg-Twocpa0-ENCN-b> a)
        (= id-1 (sample-id "reduction" "ENCN" "r"))
        (= id-1 (sample-id "cpa" "ENCN" "r"))))))

(define-fun randomness-mapping-ENCM
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((a
          (maybe-get
            (select
              (<pkg-state-Keys-<$<!n!>$>-ActiveBit>
                (<game-Twocpa0-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
                  <<game-state-Twocpa0-old>>))
              <arg-Twocpa0-ENCM-j>))))
    (and
      (= offset-0 0)
      (= offset-1 0)
      (= id-0 (sample-id "enc" "ENCM" "r"))
      (ite
        (= <arg-Twocpa0-ENCM-b> a)
        (= id-1 (sample-id "reduction" "ENCM" "r"))
        (= id-1 (sample-id "cpa" "ENCM" "r"))))))
