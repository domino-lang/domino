(define-fun randomness-mapping-GBLG
  ((id-0  SampleId)
   (id-1  SampleId)
   (offset-0 Int)
   (offset-1 Int))
  Bool
  (let ((Pkg-Keys-Bottom (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_bottom> <<game-state-LayerHybrid-old>>))
        (Pkg-Keys-Top (<game-LayerHybrid-<$<!n!><!m!><!p!>$>-pkgstate-keys_top> <<game-state-LayerHybrid-old>>)))
    (let ((zb (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Keys-Bottom))
          (zt (<pkg-state-Keys-<$<!n!>$>-z> Pkg-Keys-Top)))
      (let ((zr (not (maybe-get (select zt <arg-GBLG-r>))))
            (zl (not (maybe-get (select zt <arg-GBLG-l>))))
            (zj (maybe-get (select zb <arg-GBLG-j>))))
  (or (and (= id-0 id-1 (sample-id "keys_top" "GETAOUT" "r"))
           (= offset-0 0)
           (= offset-1 0))
      (and (= id-0 id-1 (sample-id "keys_top" "GETAOUT" "rr"))
           (= offset-0 0)
           (= offset-1 0))
      (and (= id-0 (sample-id "keys_bottom" "GETKEYSOUT" "r"))
           (= id-1 (sample-id "keys_bottom" "GETAOUT" "r"))
           (= offset-0 0)
           (= offset-1 0))
      (and (= id-0 (sample-id "keys_bottom" "GETKEYSOUT" "rr"))
           (= id-1 (sample-id "keys_bottom" "GETAOUT" "rr"))
           (= offset-0 0)
           (= offset-1 0))
      ;; Iteration 0
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_0"))
           (= offset-0 (+
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       0))                ; Offset first/second ENCN call
           (= offset-1 0))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_0"))
           (= offset-0 (+
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= offset-1 0))
      ;; Iteration 1
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_1"))
           (= offset-0 (+
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 0 2)) ; Select matching round
                       0))                ; Offset first/second ENCN call
           (= offset-1 0))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_1"))
           (= offset-0 (+
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 0 2))) ; Select matching round
           (= offset-1 0))
      ;; iteration 2
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_2"))
           (= offset-0 (+
                       (* 2 (ite zl 0 1)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       1))                ; Offset first/second ENCN call
           (= offset-1 0))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_2"))
           (= offset-0 (+
                       (ite zl 0 1)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= offset-1 0))
      ;; iteration 3
      (and (= id-0 (sample-id "enc" "ENCN" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rin_round_3"))
           (= offset-0 (+
                       (* 2 (ite zl 1 0)) ; Select matching round
                       (* 2 (ite zr 2 0)) ; Select matching round
                       1))                ; Offset first/second ENCN call
           (= offset-1 0))
      (and (= id-0 (sample-id "enc" "ENCM" "r"))
           (= id-1 (sample-id "simgate" "GBLG" "rout_round_3"))
           (= offset-0 (+
                       (ite zl 1 0)   ; Select matching round
                       (ite zr 2 0))) ; Select matching round
           (= offset-1 0)))))))