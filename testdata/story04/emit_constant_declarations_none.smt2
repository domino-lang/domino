(declare-const <<game-state-Game_MON_CCA_PKE-old>>
               <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(declare-const <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
               <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(declare-const <<theorem-consts>>
               <TheoremConsts_kem_dem_cca_ssp>)

(define-fun <<game-consts-Game_MON_CCA_PKE>>
            ()
            <GameConsts_Game_MON_CCA_PKE>
            (<gameconsts-kem_dem_cca_ssp-Game_MON_CCA_PKE> <<theorem-consts>>))

(define-fun <<game-consts-Game_MOD_CCA_PKE_Real_KEM>>
            ()
            <GameConsts_Game_MOD_CCA_PKE>
            (<gameconsts-kem_dem_cca_ssp-Game_MOD_CCA_PKE_Real_KEM> <<theorem-consts>>))

(declare-const <arg-Game_MON_CCA_PKE-PKENC-m0>
               Bits_ptl)

(declare-const <arg-Game_MOD_CCA_PKE-PKENC-m0>
               Bits_ptl)

(assert (= <arg-Game_MON_CCA_PKE-PKENC-m0>
           <arg-Game_MOD_CCA_PKE-PKENC-m0>))

(declare-const <arg-Game_MON_CCA_PKE-PKENC-m1>
               Bits_ptl)

(declare-const <arg-Game_MOD_CCA_PKE-PKENC-m1>
               Bits_ptl)

(assert (= <arg-Game_MON_CCA_PKE-PKENC-m1>
           <arg-Game_MOD_CCA_PKE-PKENC-m1>))

(declare-const <arg-Game_MON_CCA_PKE-PKDEC-c_>
               (Tuple2 Bits_kctl
                       Bits_dctl))

(declare-const <arg-Game_MOD_CCA_PKE-PKDEC-c_>
               (Tuple2 Bits_kctl
                       Bits_dctl))

(assert (= <arg-Game_MON_CCA_PKE-PKDEC-c_>
           <arg-Game_MOD_CCA_PKE-PKDEC-c_>))

(declare-const <return-Game_MON_CCA_PKE-PKGEN>
               <OracleReturn_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_PKE_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKGEN>)

(assert (= <return-Game_MON_CCA_PKE-PKGEN>
           (<oracle-Game_MON_CCA_PKE-Game_MON_CCA_PKE-MON_CCA_PKE-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKGEN> <<game-state-Game_MON_CCA_PKE-old>>
                                                                                                                                   <<game-consts-Game_MON_CCA_PKE>>)))

(declare-const return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKGEN
               (ReturnValue Bits_pkeyl))

(assert (= return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKGEN
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKGEN-return-value-or-abort> <return-Game_MON_CCA_PKE-PKGEN>)))

(declare-const <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKGEN>
               Bool)

(assert (= <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKGEN>
           (match return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKGEN
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MON_CCA_PKE-new-PKGEN>>
               <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MON_CCA_PKE-new-PKGEN>>
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKGEN-game-state> <return-Game_MON_CCA_PKE-PKGEN>)))

(declare-const <return-Game_MON_CCA_PKE-PKENC>
               <OracleReturn_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_PKE_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKENC>)

(assert (= <return-Game_MON_CCA_PKE-PKENC>
           (<oracle-Game_MON_CCA_PKE-Game_MON_CCA_PKE-MON_CCA_PKE-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKENC> <<game-state-Game_MON_CCA_PKE-old>>
                                                                                                                                   <<game-consts-Game_MON_CCA_PKE>>
                                                                                                                                   <arg-Game_MON_CCA_PKE-PKENC-m0>
                                                                                                                                   <arg-Game_MON_CCA_PKE-PKENC-m1>)))

(declare-const return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKENC
               (ReturnValue (Tuple2 Bits_kctl
                                    Bits_dctl)))

(assert (= return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKENC
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKENC-return-value-or-abort> <return-Game_MON_CCA_PKE-PKENC>)))

(declare-const <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKENC>
               Bool)

(assert (= <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKENC>
           (match return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKENC
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MON_CCA_PKE-new-PKENC>>
               <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MON_CCA_PKE-new-PKENC>>
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKENC-game-state> <return-Game_MON_CCA_PKE-PKENC>)))

(declare-const <return-Game_MON_CCA_PKE-PKDEC>
               <OracleReturn_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_PKE_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKDEC>)

(assert (= <return-Game_MON_CCA_PKE-PKDEC>
           (<oracle-Game_MON_CCA_PKE-Game_MON_CCA_PKE-MON_CCA_PKE-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKDEC> <<game-state-Game_MON_CCA_PKE-old>>
                                                                                                                                   <<game-consts-Game_MON_CCA_PKE>>
                                                                                                                                   <arg-Game_MON_CCA_PKE-PKDEC-c_>)))

(declare-const return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKDEC
               (ReturnValue Bits_ptl))

(assert (= return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKDEC
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKDEC-return-value-or-abort> <return-Game_MON_CCA_PKE-PKDEC>)))

(declare-const <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKDEC>
               Bool)

(assert (= <return-is-abort-Game_MON_CCA_PKE-MON_CCA_PKE-PKDEC>
           (match return-value-Game_MON_CCA_PKE-MON_CCA_PKE-PKDEC
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MON_CCA_PKE-new-PKDEC>>
               <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MON_CCA_PKE-new-PKDEC>>
           (<oracle-return-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MON_CCA_PKE-<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>-PKDEC-game-state> <return-Game_MON_CCA_PKE-PKDEC>)))

(declare-const <return-Game_MOD_CCA_PKE_Real_KEM-PKGEN>
               <OracleReturn_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_PKE_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKGEN>)

(assert (= <return-Game_MOD_CCA_PKE_Real_KEM-PKGEN>
           (<oracle-Game_MOD_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKGEN> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
                                                                                                                                            <<game-consts-Game_MOD_CCA_PKE_Real_KEM>>)))

(declare-const return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKGEN
               (ReturnValue Bits_pkeyl))

(assert (= return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKGEN
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKGEN-return-value-or-abort> <return-Game_MOD_CCA_PKE_Real_KEM-PKGEN>)))

(declare-const <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKGEN>
               Bool)

(assert (= <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKGEN>
           (match return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKGEN
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKGEN>>
               <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKGEN>>
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKGEN-game-state> <return-Game_MOD_CCA_PKE_Real_KEM-PKGEN>)))

(declare-const <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>
               <OracleReturn_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_PKE_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKENC>)

(assert (= <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>
           (<oracle-Game_MOD_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKENC> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
                                                                                                                                            <<game-consts-Game_MOD_CCA_PKE_Real_KEM>>
                                                                                                                                            <arg-Game_MOD_CCA_PKE-PKENC-m0>
                                                                                                                                            <arg-Game_MOD_CCA_PKE-PKENC-m1>)))

(declare-const return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKENC
               (ReturnValue (Tuple2 Bits_kctl
                                    Bits_dctl)))

(assert (= return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKENC
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKENC-return-value-or-abort> <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>)))

(declare-const <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKENC>
               Bool)

(assert (= <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKENC>
           (match return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKENC
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKENC>>
               <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKENC>>
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKENC-game-state> <return-Game_MOD_CCA_PKE_Real_KEM-PKENC>)))

(declare-const <return-Game_MOD_CCA_PKE_Real_KEM-PKDEC>
               <OracleReturn_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_PKE_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKDEC>)

(assert (= <return-Game_MOD_CCA_PKE_Real_KEM-PKDEC>
           (<oracle-Game_MOD_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKDEC> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>
                                                                                                                                            <<game-consts-Game_MOD_CCA_PKE_Real_KEM>>
                                                                                                                                            <arg-Game_MOD_CCA_PKE-PKDEC-c_>)))

(declare-const return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKDEC
               (ReturnValue Bits_ptl))

(assert (= return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKDEC
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKDEC-return-value-or-abort> <return-Game_MOD_CCA_PKE_Real_KEM-PKDEC>)))

(declare-const <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKDEC>
               Bool)

(assert (= <return-is-abort-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKDEC>
           (match return-value-Game_MOD_CCA_PKE_Real_KEM-MOD_CCA_PKE-PKDEC
                  (((mk-return-value returnvalue)
                    false)
                   (mk-abort true)))))

(declare-const <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKDEC>>
               <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)

(assert (= <<game-state-Game_MOD_CCA_PKE_Real_KEM-new-PKDEC>>
           (<oracle-return-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-MOD_CCA_PKE-<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>-PKDEC-game-state> <return-Game_MOD_CCA_PKE_Real_KEM-PKDEC>)))

(declare-const randctr-Game_MON_CCA_PKE-0
               Int)

(assert (= randctr-Game_MON_CCA_PKE-0
           (<game-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-rand-Scheme_KEM-KEM_GEN-kem_gen> <<game-state-Game_MON_CCA_PKE-old>>)))

(assert (= randctr-Game_MON_CCA_PKE-0
           0))

(declare-const randctr-Game_MON_CCA_PKE-1
               Int)

(assert (= randctr-Game_MON_CCA_PKE-1
           (<game-Game_MON_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-rand-Scheme_KEM-KEM_ENCAPS-kem_encaps> <<game-state-Game_MON_CCA_PKE-old>>)))

(assert (= randctr-Game_MON_CCA_PKE-1
           0))

(declare-const randctr-Game_MOD_CCA_PKE_Real_KEM-0
               Int)

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-0
           (<game-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-rand-Key-SET-1> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>)))

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-0
           0))

(declare-const randctr-Game_MOD_CCA_PKE_Real_KEM-1
               Int)

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-1
           (<game-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-rand-Scheme_KEM-KEM_GEN-kem_gen> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>)))

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-1
           0))

(declare-const randctr-Game_MOD_CCA_PKE_Real_KEM-2
               Int)

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-2
           (<game-Game_MOD_CCA_PKE-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-rand-Scheme_KEM-KEM_ENCAPS-kem_encaps> <<game-state-Game_MOD_CCA_PKE_Real_KEM-old>>)))

(assert (= randctr-Game_MOD_CCA_PKE_Real_KEM-2
           0))
