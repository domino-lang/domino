(define-fun randomness-mapping-GETAOUT
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  Int)
   (id-1  Int)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  (and
   ;;(= base-ctr-0 scr-0)
   ;;(= base-ctr-1 scr-1)
   (= id-0 id-1)))

(define-fun randomness-mapping-SETBIT
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  Int)
   (id-1  Int)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  false)


;; <arg-GBLG-r>
;; <<game-state-Left_inst-old>>
;;
;; keys_bottom.z[r]
(define-fun randomness-mapping-GBLG
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  Int)
   (id-1  Int)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  (let ((Pkg-Keys-Bottom (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> <<game-state-LeftDebug_inst-old>>))
        (Pkg-Keys-Top (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> <<game-state-LeftDebug_inst-old>>)))
    (let ((zb (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Keys-Bottom))
          (zt (<pkg-state-GenericKeys-<$<!n!>$>-z> Pkg-Keys-Top)))
      (let ((zr (maybe-get (select zt <arg-GBLG-r>)))
            (zl (maybe-get (select zt <arg-GBLG-l>)))
            (zj (maybe-get (select zb <arg-GBLG-j>))))
  (or (and (= id-0 id-1 0)
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 id-1 1)
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 (+ id-1 2) 6)
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      (and (= id-0 (+ id-1 2) 7)
           (= base-ctr-0 scr-0)
           (= base-ctr-1 scr-1))
      ;; Iteration 0
      ;; Right: First iteration 
      ;; Right: false, false
      ;; Left: Kl[zl], Kr[zr]
      ;; Left: 
      (and (= id-0 8)
           (= id-1 8)
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       (ite zr 0 1)))     ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 9)
           (= id-1 9)
           (= scr-0 (+ base-ctr-0
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; Iteration 1
      (and (= id-0 8)
           (= id-1 10)
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       (ite zr 0 1)))     ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 9)
           (= id-1 11)
           (= scr-0 (+ base-ctr-0
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; iteration 2
      (and (= id-0 8)
           (= id-1 12)
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       (ite zr 1 0)))     ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 9)
           (= id-1 13)
           (= scr-0 (+ base-ctr-0
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= base-ctr-1 scr-1))
      ;; iteration 3
      (and (= id-0 8)
           (= id-1 14)
           (= scr-0 (+ base-ctr-0
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       (ite zr 1 0)))     ; Offset first/second ENCN call
           (= base-ctr-1 scr-1))
      (and (= id-0 9)
           (= id-1 15)
           (= scr-0 (+ base-ctr-0
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= base-ctr-1 scr-1)))))))


(define-fun randomness-mapping-GETKEYSIN
  ((base-ctr-0 Int)
   (base-ctr-1 Int)
   (id-0  Int)
   (id-1  Int)
   (scr-0 Int)
   (scr-1 Int))
  Bool
  false)


(define-fun <relation-aborts-LeftDebug_inst-RightDebug_inst-GBLG>
    ((State-Left  <GameState_LeftDebug_<$<!n!><!m!><!p!>$>>)
     (State-Right <GameState_RightDebug_<$<!n!><!m!><!p!>$>>)
     (Return-Left  <OracleReturn_LeftDebug_<$<!n!><!m!><!p!>$>_GateDebug_<$<!0!><!m!><!n!><!p!>$>_GBLG>)
     (Return-Right <OracleReturn_RightDebug_<$<!n!><!m!><!p!>$>_SimgateDebug_<$<!m!><!n!><!p!>$>_GBLG>)
     (l Int)
     (r Int)
     (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
     (j Int))
  Bool
  (let ((Return-Value-Left (<oracle-return-LeftDebug-<$<!n!><!m!><!p!>$>-GateDebug-<$<!0!><!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Left))
        (Return-Value-Right (<oracle-return-RightDebug-<$<!n!><!m!><!p!>$>-SimgateDebug-<$<!m!><!n!><!p!>$>-GBLG-return-value-or-abort> Return-Right)))
    (let ((Pkg-Left-Keys-Top (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Left))
          (Pkg-Left-Keys-Bottom (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Left))
          (Pkg-Right-Keys-Top (<game-RightDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> State-Right))
          (Pkg-Right-Keys-Bottom (<game-RightDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> State-Right)))
      (let ((Left-Top-T (<pkg-state-GenericKeys-<$<!n!>$>-T> Pkg-Left-Keys-Top))
            (Left-Top-z (<pkg-state-GenericKeys-<$<!n!>$>-z> Pkg-Left-Keys-Top))
            (Left-Top-flag (<pkg-state-GenericKeys-<$<!n!>$>-flag> Pkg-Left-Keys-Top))
            (Left-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Bottom))
            (Left-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Bottom))
            (Left-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Bottom))
            (Right-Top-T (<pkg-state-GenericKeys-<$<!n!>$>-T> Pkg-Right-Keys-Top))
            (Right-Top-z (<pkg-state-GenericKeys-<$<!n!>$>-z> Pkg-Right-Keys-Top))
            (Right-Top-flag (<pkg-state-GenericKeys-<$<!n!>$>-flag> Pkg-Right-Keys-Top))
            (Right-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Bottom))
            (Right-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Bottom))
            (Right-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Bottom)))
        (and
         (= (or (is-mk-none (select Left-Top-T r))
                (is-mk-none (select Left-Top-T l))
                (= (select Left-Bottom-flag j) (mk-some true))
                (exists ((left Bool) (right Bool)) (is-mk-none (select op (mk-tuple2 left right)))))
            (is-mk-abort Return-Value-Left))
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
    ((left-game <GameState_LeftDebug_<$<!n!><!m!><!p!>$>>)
     (right-game <GameState_RightDebug_<$<!n!><!m!><!p!>$>>))
  Bool
  (let ((Pkg-Left-Keys-Top (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> left-game))
        (Pkg-Right-Keys-Top  (<game-RightDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> right-game))
        (Pkg-Left-Keys-Bottom  (<game-LeftDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> left-game))
        (Pkg-Right-Keys-Bottom  (<game-RightDebug-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> right-game)))
          (let ((Left-Top-T (<pkg-state-GenericKeys-<$<!n!>$>-T> Pkg-Left-Keys-Top))
            (Left-Top-z (<pkg-state-GenericKeys-<$<!n!>$>-z> Pkg-Left-Keys-Top))
            (Left-Top-flag (<pkg-state-GenericKeys-<$<!n!>$>-flag> Pkg-Left-Keys-Top))
            (Left-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Left-Keys-Bottom))
            (Left-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Left-Keys-Bottom))
            (Left-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Left-Keys-Bottom))
            (Right-Top-T (<pkg-state-GenericKeys-<$<!n!>$>-T> Pkg-Right-Keys-Top))
            (Right-Top-z (<pkg-state-GenericKeys-<$<!n!>$>-z> Pkg-Right-Keys-Top))
            (Right-Top-flag (<pkg-state-GenericKeys-<$<!n!>$>-flag> Pkg-Right-Keys-Top))
            (Right-Bottom-T (<pkg-state-Keys-<$<!n!>$>-T> Pkg-Right-Keys-Bottom))
            (Right-Bottom-z (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Right-Keys-Bottom))
            (Right-Bottom-flag (<pkg-state-Keys-<$<!n!>$>-flag> Pkg-Right-Keys-Bottom)))

    (and
     (= Left-Top-T Right-Top-T)
     (= Left-Top-z Right-Top-z)
     (= Left-Bottom-T Right-Bottom-T)

     (wellformed-T Left-Top-T)
     (wellformed-T Right-Top-T)
     (wellformed-T Left-Bottom-T)
     (wellformed-T Right-Bottom-T)

     (aout-key-package Left-Top-T Left-Top-z Left-Top-flag)
     (aout-key-package Left-Bottom-T Left-Bottom-flag Left-Bottom-flag) ; z might not be set but flag is so cheating :-)
     (aout-key-package Right-Top-T Right-Top-z Right-Top-flag)
     (aout-key-package Right-Bottom-T Right-Bottom-z Right-Bottom-flag)

     (forall ((i Int)) (= (is-mk-none (select Right-Bottom-z i)) (not (= (mk-some true) (select Left-Bottom-flag i)))))))))
