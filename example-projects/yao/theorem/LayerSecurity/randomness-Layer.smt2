(define-randomness-mapping GBLG
  (left right consts)
  (let ((zl (not (maybe-get (select left.state.keys_top.z left.args.l))))
        (zr (not (maybe-get (select left.state.keys_top.z left.args.r)))))
     (or (and (= left.id right.id (sample-id "keys_top" "GETAOUT" "r"))
               (= left.ctr 0)
               (= right.ctr 0))
          (and (= left.id right.id (sample-id "keys_top" "GETAOUT" "rr"))
               (= left.ctr 0)
               (= right.ctr 0))
          (and (= left.id (sample-id "keys_bottom" "GETKEYSOUT" "r"))
               (= right.id (sample-id "keys_bottom" "GETAOUT" "r"))
               (= left.ctr 0)
               (= right.ctr 0))
          (and (= left.id (sample-id "keys_bottom" "GETKEYSOUT" "rr"))
               (= right.id (sample-id "keys_bottom" "GETAOUT" "rr"))
               (= left.ctr 0)
               (= right.ctr 0))
          ;; Iteration 0
          (and (= left.id (sample-id "enc" "ENCN" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rin_round_0"))
               (= left.ctr (+
                         (* 2 (ite zl 0 1)) ; Select matching round
                         (* 2 (ite zr 0 2)) ; Select matching round
                         0))                ; Offset first/second ENCN call
               (= right.ctr 0))
          (and (= left.id (sample-id "enc" "ENCM" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rout_round_0"))
               (= left.ctr (+
                         (ite zl 0 1)   ; Select matching round
                         (ite zr 0 2))) ; Select matching round
               (= right.ctr 0))
          ;; Iteration 1
          (and (= left.id (sample-id "enc" "ENCN" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rin_round_1"))
               (= left.ctr (+
                         (* 2 (ite zl 1 0)) ; Select matching round
                         (* 2 (ite zr 0 2)) ; Select matching round
                         0))                ; Offset first/second ENCN call
               (= right.ctr 0))
          (and (= left.id (sample-id "enc" "ENCM" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rout_round_1"))
               (= left.ctr (+
                         (ite zl 1 0)   ; Select matching round
                         (ite zr 0 2))) ; Select matching round
               (= right.ctr 0))
          ;; iteration 2
          (and (= left.id (sample-id "enc" "ENCN" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rin_round_2"))
               (= left.ctr (+
                         (* 2 (ite zl 0 1)) ; Select matching round
                         (* 2 (ite zr 2 0)) ; Select matching round
                         1))                ; Offset first/second ENCN call
               (= right.ctr 0))
          (and (= left.id (sample-id "enc" "ENCM" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rout_round_2"))
               (= left.ctr (+
                         (ite zl 0 1)   ; Select matching round
                         (ite zr 2 0))) ; Select matching round
               (= right.ctr 0))
          ;; iteration 3
          (and (= left.id (sample-id "enc" "ENCN" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rin_round_3"))
               (= left.ctr (+
                         (* 2 (ite zl 1 0)) ; Select matching round
                         (* 2 (ite zr 2 0)) ; Select matching round
                         1))                ; Offset first/second ENCN call
               (= right.ctr 0))
          (and (= left.id (sample-id "enc" "ENCM" "r"))
               (= right.id (sample-id "simgate" "GBLG" "rout_round_3"))
               (= left.ctr (+
                         (ite zl 1 0)   ; Select matching round
                         (ite zr 2 0))) ; Select matching round
               (= right.ctr 0)))))