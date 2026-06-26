(define-state-relation invariant
    (
        (left <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>) ; left
        (right <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>) ; right
    )
    (and
        ; left_pk = right_pk
        (= left.MON_CCA_PKE.pk right.MOD_CCA_PKE.pk right.KEM.pk) 
        ; left_pk = None iff right_pk = None
        (= (is-mk-none left.MON_CCA_PKE.pk) 
           (is-mk-none left.MON_CCA_PKE.sk) 
           (is-mk-none right.MOD_CCA_PKE.pk) 
           (is-mk-none right.KEM.pk) 
           (is-mk-none right.KEM.sk)) 
        ; left_c = right_c
        (= left.MON_CCA_PKE.c right.MOD_CCA_PKE.c) 
        ; left_c = None iff right_c = None iff right_kem_c = None iff right_key_k = None
        (= (is-mk-none left.MON_CCA_PKE.c) 
           (is-mk-none right.MOD_CCA_PKE.c) 
           (is-mk-none right.KEM.c) 
           (is-mk-none right.Key.k)
           (is-mk-none right.DEM.c))
        ; left_sk = right_sk
        (= left.MON_CCA_PKE.sk right.KEM.sk)
        ; if PKGEN is not called, PKENC can not be called
        (=> (is-mk-none right.KEM.pk)
            (is-mk-none right.MOD_CCA_PKE.c)) 
        (=>
            (not (is-mk-none right.MOD_CCA_PKE.c))
            (and
                (= (maybe-get right.KEM.c) (el2-1 (maybe-get right.MOD_CCA_PKE.c)))
                (= (maybe-get right.DEM.c) (el2-2 (maybe-get right.MOD_CCA_PKE.c)))
            )
        )
        (=>
            (not (is-mk-none right.Key.k))
            (= (maybe-get right.Key.k) (<<func-kem_decaps>> (maybe-get right.KEM.sk) (maybe-get right.KEM.c)))
        )
    )
)

(define-lemma <relation-lemma-kem-correctness-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKENC>
    (
        (old-state-left <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (old-state-right <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (return-left <OracleReturn_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_PKE_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKENC>)
        (return-right <OracleReturn_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_PKE_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKENC>)
        (m0 Bits_ptl)
        (m1 Bits_ptl)
    )
    (=>
        (not (is-mk-none old-state-right.KEM.pk))
        (forall 
            (
                (r Bits_kencr)
            )
            (let
                (
                    (k (el2-1 (<<func-kem_encaps>> r (maybe-get old-state-right.KEM.pk))))
                    (ek (el2-2 (<<func-kem_encaps>> r (maybe-get old-state-right.KEM.pk))))
                )
                (= k (<<func-kem_decaps>> (maybe-get old-state-right.KEM.sk) ek))
            )
        )
    )
)

(define-lemma <relation-lemma-kem-correctness-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (old-state-right <GameState_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (return-left <OracleReturn_Game_MON_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_PKE_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKDEC>)
        (return-right <OracleReturn_Game_MOD_CCA_PKE_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_PKE_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKDEC>)
        (ek_ctxt (Tuple2 Bits_kctl Bits_dctl))
    )
    (=>
        (not (is-mk-none old-state-right.KEM.pk))
        (forall 
            (
                (r Bits_kencr)
            )
            (let
                (
                    (k (el2-1 (<<func-kem_encaps>> r (maybe-get old-state-right.KEM.pk))))
                    (ek (el2-2 (<<func-kem_encaps>> r (maybe-get old-state-right.KEM.pk))))
                )
                (= k (<<func-kem_decaps>> (maybe-get old-state-right.KEM.sk) ek))
            )
        )
    )
)
