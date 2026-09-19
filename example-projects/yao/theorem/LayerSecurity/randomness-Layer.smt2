(define-fun randomness-mapping-GarbleGate
  ((id-0 SampleId)
   (id-1 SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  ;; Left game:  LayerHybrid (Gate + real-or-zeros Enc1)
  ;; Right game: LayerIdeal  (Simgate)
  ;;
  ;; The four rows of the garbled gate are produced by Gate in the fixed order
  ;;   row 0 = (bl, br) = (false, false)   row 1 = (true,  false)
  ;;   row 2 = (bl, br) = (false, true)    row 3 = (true,  true)
  ;; so EncInner and EncOuter are each called once per row and the sample offset of a
  ;; row equals its index (bl ? 1 : 0) + (br ? 2 : 0).
  ;;
  ;; With real-or-zeros encryption only six of those eight ciphertexts carry
  ;; randomness that reaches the output:
  ;;   * the row (bl, br) = (la, ra)        -- both keys active: inner + outer
  ;;   * the row (bl, br) = (not la, ra)    -- outer key active: inner + outer
  ;;   * the two rows with br = not ra      -- the outer encryption of zeros
  ;;     swallows the inner ciphertext, so only the outer coin matters and the
  ;;     two inner EncInner coins of those rows stay unmapped.
  ;; Those six line up with the six coins drawn by Simgate.
  (let ((keys-top
          (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top>
            <<game-state-LayerHybrid-old>>)))
    (let ((active-bit (<pkg-state-Keys-<$<!n!>$>-ActiveBit> keys-top)))
      (let ((left-active
              (maybe-get (select active-bit <arg-LayerHybrid-GarbleGate-left_input>)))
            (right-active
              (maybe-get (select active-bit <arg-LayerHybrid-GarbleGate-right_input>))))
        (or
          ;; Sampling performed by the key packages is independent of the
          ;; active input bits.
          (and (= id-0 id-1 (sample-id "keys_top" "GenerateWireKeys" "key_true"))
               (= offset-0 0)
               (= offset-1 0))
          (and (= id-0 id-1 (sample-id "keys_top" "GenerateWireKeys" "key_false"))
               (= offset-0 0)
               (= offset-1 0))
          (and (= id-0 (sample-id "keys_bottom" "GenerateWireKeys" "key_true"))
               (= id-1 (sample-id "keys_bottom" "GenerateWireKeys" "key_true"))
               (= offset-0 0)
               (= offset-1 0))
          (and (= id-0 (sample-id "keys_bottom" "GenerateWireKeys" "key_false"))
               (= id-1 (sample-id "keys_bottom" "GenerateWireKeys" "key_false"))
               (= offset-0 0)
               (= offset-1 0))

          ;; Active input bits: (false, false).
          (and (not left-active)
               (not right-active)
               (or
                 ;; the active row: real inner and outer encryption
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_active"))
                      (= offset-0 0) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_active"))
                      (= offset-0 0) (= offset-1 0))
                 ;; inactive left key inside, active right key outside
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_inactive"))
                      (= offset-0 1) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_inactive"))
                      (= offset-0 1) (= offset-1 0))
                 ;; inactive right key outside: encryptions of zeros
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_0"))
                      (= offset-0 2) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_1"))
                      (= offset-0 3) (= offset-1 0))))

          ;; Active input bits: (false, true).
          (and (not left-active)
               right-active
               (or
                 ;; the active row: real inner and outer encryption
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_active"))
                      (= offset-0 2) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_active"))
                      (= offset-0 2) (= offset-1 0))
                 ;; inactive left key inside, active right key outside
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_inactive"))
                      (= offset-0 3) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_inactive"))
                      (= offset-0 3) (= offset-1 0))
                 ;; inactive right key outside: encryptions of zeros
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_0"))
                      (= offset-0 0) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_1"))
                      (= offset-0 1) (= offset-1 0))))

          ;; Active input bits: (true, false).
          (and left-active
               (not right-active)
               (or
                 ;; the active row: real inner and outer encryption
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_active"))
                      (= offset-0 1) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_active"))
                      (= offset-0 1) (= offset-1 0))
                 ;; inactive left key inside, active right key outside
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_inactive"))
                      (= offset-0 0) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_inactive"))
                      (= offset-0 0) (= offset-1 0))
                 ;; inactive right key outside: encryptions of zeros
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_0"))
                      (= offset-0 2) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_1"))
                      (= offset-0 3) (= offset-1 0))))

          ;; Active input bits: (true, true).
          (and left-active
               right-active
               (or
                 ;; the active row: real inner and outer encryption
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_active"))
                      (= offset-0 3) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_active"))
                      (= offset-0 3) (= offset-1 0))
                 ;; inactive left key inside, active right key outside
                 (and (= id-0 (sample-id "enc" "EncInner" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rin_inactive"))
                      (= offset-0 2) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_inactive"))
                      (= offset-0 2) (= offset-1 0))
                 ;; inactive right key outside: encryptions of zeros
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_0"))
                      (= offset-0 0) (= offset-1 0))
                 (and (= id-0 (sample-id "enc" "EncOuter" "r"))
                      (= id-1 (sample-id "simgate" "SimulateGarbledGate" "rout_zero_1"))
                      (= offset-0 1) (= offset-1 0)))))))))
