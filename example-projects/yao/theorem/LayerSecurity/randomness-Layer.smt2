(define-randomness-mapping GBLG
  (left right consts)
  (let ((id-0 left.id)
        (id-1 right.id)
        (offset-0 left.ctr)
        (offset-1 right.ctr)
        (zl (not (maybe-get (select left.state.keys_top.z left.args.l))))
        (zr (not (maybe-get (select left.state.keys_top.z left.args.r)))))
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
               (= offset-1 0)))))