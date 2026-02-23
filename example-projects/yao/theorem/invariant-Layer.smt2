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

(define-fun wellformed-T
    ((T (Array Int (Maybe (Array Bool (Maybe Bits_n))))))
  Bool
  (forall ((i Int) (b Bool))
          (=> (not (is-mk-none (select T i)))
              (not (is-mk-none (select (maybe-get (select T i)) b))))))

(define-state-relation invariant
     (
          (left-game <GameState_LayerHybrid_<$<!n!><!m!><!p!>$>>)
          (right-game <GameState_LayerIdeal_<$<!n!><!m!><!p!>$>>)
     )
     (and
          (= left-game.keys_top.T right-game.keys_top.T)
          (= left-game.keys_top.z right-game.keys_top.z)
          (= left-game.keys_top.flag right-game.keys_top.flag)
          (= left-game.keys_bottom.T right-game.keys_bottom.T)
          (= left-game.keys_bottom.flag right-game.keys_bottom.flag)

          (wellformed-T left-game.keys_bottom.T)

          (forall ((i Int)) 
               (= 
                    (is-mk-none (select right-game.keys_bottom.z i)) 
                    (not (= (mk-some true) (select left-game.keys_bottom.flag i)))
               )
          )
     )
)