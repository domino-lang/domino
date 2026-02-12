(define-fun randomness-mapping-GETAOUT
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  SampleId)
   (id-1  SampleId)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  (and
   (= base-ctr-0 scr-0)
   (= base-ctr-1 scr-1)
   (= id-0 id-1)))

(define-fun randomness-mapping-SETBIT
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  SampleId)
   (id-1  SampleId)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  false)


(define-fun randomness-mapping-GBLG
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  SampleId)
   (id-1  SampleId)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  (let ((Pkg-Keys-Bottom (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> <<game-state-LayerHybrid-old>>))
        (Pkg-Keys-Top (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> <<game-state-LayerHybrid-old>>)))
    (let ((zb (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Keys-Bottom))
          (zt (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Keys-Top)))
      (let ((zr (not (maybe-get (select zt <arg-GBLG-r>))))
            (zl (not (maybe-get (select zt <arg-GBLG-l>))))
            (zj (maybe-get (select zb <arg-GBLG-j>))))
  (or (and (= id-0 id-1 (sample-id "keys_top" "GETAOUT" "r"))
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 id-1 (sample-id "keys_top" "GETAOUT" "rr"))
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "keys_bottom" "GETKEYSOUT" "r"))
           (= id-1 (sample-id "keys_bottom" "GETAOUT" "r"))
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "keys_bottom" "GETKEYSOUT" "rr"))
           (= id-1 (sample-id "keys_bottom" "GETAOUT" "rr"))
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      ;; Iteration 0
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_0"))
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       0))                ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_0"))
           (= scr-0 (+ base-ctr-0
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; Iteration 1
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_1"))
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       0))                ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_1"))
           (= scr-0 (+ base-ctr-0
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; iteration 2
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_2"))
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       1))                ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_2"))
           (= scr-0 (+ base-ctr-0
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; iteration 3
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_3"))
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       1))                ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_3"))
           (= scr-0 (+ base-ctr-0
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= base-ctr-1 scr-1)))))))


(define-fun randomness-mapping-GETKEYSIN
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  SampleId)
   (id-1  SampleId)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  false)


(define-fun <relation-aborts-LayerHybrid-LayerIdeal-GBLG>
    ((State-Left  <GameState_LayerHybrid_<$<!n!><!m!><!p!>$>>)
     (State-Right <GameState_LayerIdeal_<$<!n!><!m!><!p!>$>>)
     (Return-Left  <OracleReturn_LayerHybrid_<$<!n!><!m!><!p!>$>_Gate_<$<!m!><!n!><!p!>$>_GBLG>)
     (Return-Right <OracleReturn_LayerIdeal_<$<!n!><!m!><!p!>$>_Simgate_<$<!m!><!n!><!p!>$>_GBLG>)
     (l Int)
     (r Int)
     (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
     (j Int))
  Bool
  (let ((Return-Value-Left (<oracle-return-LayerHybrid-<$<!n!><!m!><!p!>$>-Gate-<$<!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Left))
        (Return-Value-Right (<oracle-return-LayerIdeal-<$<!n!><!m!><!p!>$>-Simgate-<$<!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Right)))
    (let ((Pkg-Left-Keys-Top (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Left))
          (Pkg-Left-Keys-Bottom (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Left))
          (Pkg-Right-Keys-Top (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Right))
          (Pkg-Right-Keys-Bottom (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Right)))
      (let ((Left-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Top))
            (Left-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Top))
            (Left-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Top))
            (Left-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Bottom))
            (Left-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Bottom))
            (Left-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Bottom))
            (Right-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Top))
            (Right-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Top))
            (Right-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Top))
            (Right-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Bottom))
            (Right-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Bottom))
            (Right-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Bottom)))
        (and
         ;; Left Aborts
         (= (or (is-mk-none (select Left-Top-T r))
                (is-mk-none (select Left-Top-T l))
                (= (select Left-Bottom-flag j) (mk-some true))
                (exists ((left Bool) (right Bool)) (is-mk-none (select op (mk-tuple2 left right)))))
            (is-mk-abort Return-Value-Left))
         ;; Right Aborts
         (= (or (is-mk-none (select Right-Top-T r))
                 (is-mk-none (select Right-Top-T l))
                 (not (is-mk-none (select Right-Bottom-z j)))
                 (exists ((left Bool) (right Bool)) (is-mk-none (select op (mk-tuple2 left right)))))
             (is-mk-abort Return-Value-Right)))))))




            


(define-fun aout-key-package
    ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
     (z (Array Int (Maybe Bool)))
     (flag (Array Int (Maybe Bool))))
  Bool
  (forall ((i Int))
          (=> (not (is-mk-none (select T i)))
              (and (not (is-mk-none (select z i)))
                   (= (select flag i) (mk-some true))))))



(define-fun wellformed-T
    ((T (Array Int (Maybe (Array Bool (Maybe Bits_n))))))
  Bool
  (forall ((i Int) (b Bool))
          (=> (not (is-mk-none (select T i)))
              (not (is-mk-none (select (maybe-get (select T i)) b))))))




(define-fun invariant
    ((left-game <GameState_LayerHybrid_<$<!n!><!m!><!p!>$>>)
     (right-game <GameState_LayerIdeal_<$<!n!><!m!><!p!>$>>))
  Bool
  (let ((Pkg-Left-Keys-Top (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> left-game))
        (Pkg-Right-Keys-Top  (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> right-game))
        (Pkg-Left-Keys-Bottom  (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> left-game))
        (Pkg-Right-Keys-Bottom  (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> right-game)))
    (let ((Left-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Top))
          (Left-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Top))
          (Left-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Top))
          (Left-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Bottom))
          (Left-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Bottom))
          (Left-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Bottom))
          (Right-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Top))
          (Right-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Top))
          (Right-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Top))
          (Right-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Bottom))
          (Right-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Bottom))
          (Right-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Bottom)))

    (and
     (= Left-Top-T Right-Top-T)
     (= Left-Top-z Right-Top-z)
     (= Left-Top-flag Right-Top-flag)
     (= Left-Bottom-T Right-Bottom-T)
     (= Left-Bottom-flag Right-Bottom-flag)

     (wellformed-T Left-Top-T) ; for left aborts
     (wellformed-T Right-Top-T) ; for right aborts
     (wellformed-T Left-Bottom-T) ; for left aborts
     (wellformed-T Right-Bottom-T) ; for right aborts

     (aout-key-package Left-Top-T Left-Top-z Left-Top-flag) ; for left aborts
     (aout-key-package Right-Top-T Right-Top-z Right-Top-flag) ; for right aborts

     ;(forall ((i Int)) (= (is-mk-none (select Right-Bottom-z i)) (not (= (mk-some true) (select Right-Bottom-flag i))))) ; also works
     (forall ((i Int)) (= (is-mk-none (select Right-Bottom-z i)) (not (= (mk-some true) (select Left-Bottom-flag i)))))))))


(define-fun <relation-debug-LayerHybrid-LayerIdeal-GBLG>
    ((State-Left-Old  <GameState_LayerHybrid_<$<!n!><!m!><!p!>$>>)
     (State-Right-Old <GameState_LayerIdeal_<$<!n!><!m!><!p!>$>>)
     (Return-Left  <OracleReturn_LayerHybrid_<$<!n!><!m!><!p!>$>_Gate_<$<!m!><!n!><!p!>$>_GBLG>)
     (Return-Right <OracleReturn_LayerIdeal_<$<!n!><!m!><!p!>$>_Simgate_<$<!m!><!n!><!p!>$>_GBLG>)
     (l Int)
     (r Int)
     (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
     (j Int))
  Bool
  (let ((Return-Value-Left (<oracle-return-LayerHybrid-<$<!n!><!m!><!p!>$>-Gate-<$<!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Left))
        (State-Left (<oracle-return-LayerHybrid-<$<!n!><!m!><!p!>$>-Gate-<$<!m!><!n!><!p!>$>-GBLG-game-state> Return-Left))
        (Return-Value-Right (<oracle-return-LayerIdeal-<$<!n!><!m!><!p!>$>-Simgate-<$<!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Right))
        (State-Right (<oracle-return-LayerIdeal-<$<!n!><!m!><!p!>$>-Simgate-<$<!m!><!n!><!p!>$>-GBLG-game-state> Return-Right)))
    (let ((Pkg-Left-Keys-Top (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Left))
          (Pkg-Left-Keys-Bottom (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Left))
          (Pkg-Right-Keys-Top (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Right))
          (Pkg-Right-Keys-Bottom (<game-LayerIdeal-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Right)))
      (let ((Left-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Top))
            (Left-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Top))
            (Left-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Top))
            (Left-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Bottom))
            (Left-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Bottom))
            (Left-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Bottom))
            (Right-Top-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Top))
            (Right-Top-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Top))
            (Right-Top-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Top))
            (Right-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Bottom))
            (Right-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Bottom))
            (Right-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Bottom)))
        (let ((right-keys (maybe-get (select Right-Top-T r)))
              (right-z (maybe-get (select Right-Top-z r)))
              (right-retval (return-value Return-Value-Right))
              (left-keys (maybe-get (select Right-Top-T l)))
              (left-z (maybe-get (select Right-Top-z l)))
              (left-retval (return-value Return-Value-Left)))
          (let ((right-active (maybe-get (select right-keys right-z)))
                (right-inactive (maybe-get (select right-keys (not right-z))))
                (left-active (maybe-get (select left-keys left-z)))
                (left-inactive (maybe-get (select left-keys (not left-z)))))
            (and true

                 ;; (= Left-Top-T Right-Top-T)
                 ;; (= Left-Top-z Right-Top-z)
                 (= Left-Bottom-T Right-Bottom-T)

                 (wellformed-T Left-Top-T)
                 (wellformed-T Right-Top-T)
                 (wellformed-T Left-Bottom-T)
                 (wellformed-T Right-Bottom-T)

                 (aout-key-package Left-Top-T Left-Top-z Left-Top-flag)
                 (aout-key-package Left-Bottom-T Left-Bottom-flag Left-Bottom-flag)
                 (aout-key-package Right-Top-T Right-Top-z Right-Top-flag)
                 (aout-key-package Right-Bottom-T Right-Bottom-z Right-Bottom-flag)

                 (forall ((i Int)) (= (is-mk-none (select Right-Bottom-z i)) (not (= (mk-some true) (select Left-Bottom-flag i)))))

                 )))))))
