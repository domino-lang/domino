(define-state-relation invariant
    (
        (left <GameState_MonolithicPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>) ; left
        (right <GameState_ModularPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>) ; right
    )
    (and
        ; left_pk = right_pk
        (= left.MON_CCA.pk right.MOD_CCA.pk right.KEM.pk) 
        ; left_pk = None iff right_pk = None
        (= (is-mk-none left.MON_CCA.pk) 
           (is-mk-none left.MON_CCA.sk) 
           (is-mk-none right.MOD_CCA.pk) 
           (is-mk-none right.KEM.pk) 
           (is-mk-none right.KEM.sk)) 
        ; left_c = right_c
        (= left.MON_CCA.c right.MOD_CCA.c) 
        ; left_c = None iff right_c = None iff right_kem_c = None iff right_key_k = None
        (= (is-mk-none left.MON_CCA.c) 
           (is-mk-none right.MOD_CCA.c) 
           (is-mk-none right.KEM.c) 
           (is-mk-none right.Key.k)
           (is-mk-none right.DEM.c))
        ; left_sk = right_sk
        (= left.MON_CCA.sk right.KEM.sk)
        ; if PKGEN is not called, PKENC can not be called
        (=> (is-mk-none right.KEM.pk)
            (is-mk-none right.MOD_CCA.c)) 
        (=>
            (not (is-mk-none right.MOD_CCA.c))
            (and
                (= (maybe-get right.KEM.c) (el2-1 (maybe-get right.MOD_CCA.c)))
                (= (maybe-get right.DEM.c) (el2-2 (maybe-get right.MOD_CCA.c)))
            )
        )
        (=>
            (not (is-mk-none right.Key.k))
            (and
                (= (maybe-get right.Key.k) (el2-1 (<<func-kem_encaps>> (maybe-get right.KEM.encaps_randomness) (maybe-get right.KEM.pk))))
                (= (maybe-get right.KEM.c) (el2-2 (<<func-kem_encaps>> (maybe-get right.KEM.encaps_randomness) (maybe-get right.KEM.pk))))
            )
        )
    )
)

; The following axiom gives unknown when checking satisfiability of only invariants
;(assert
;    (forall 
;        (
;            (gen-r Bits_kgenr)
;            (encaps-r Bits_kencr)
;        )
;        (let 
;            (
;                (pk (el2-1 (<<func-kem_gen>> gen-r)))
;                (sk (el2-2 (<<func-kem_gen>> gen-r)))
;            )
;            (let
;                (
;                    (k (el2-1 (<<func-kem_encaps>> encaps-r pk)))
;                    (ek (el2-2 (<<func-kem_encaps>> encaps-r pk)))
;                )
;                (= k (<<func-kem_decaps>> sk ek))
;            )
;        )
;    )
;)

(define-fun <relation-lemma-kem-correctness-monolithic_pke_cca_game-modular_pke_cca_game_with_real_kem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (old-state-right <GameState_ModularPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>>)
        (return-left <OracleReturn_MonolithicPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MON_CCA_<$<!dctl!><!kctl!><!pkeyl!><!ptl!><!skeyl!>$>_PKDEC>)
        (return-right <OracleReturn_ModularPkeCcaGame_<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>_MOD_CCA_<$<!dctl!><!dkeyl!><!kctl!><!pkeyl!><!ptl!>$>_PKDEC>)
        (ek_ctxt (Tuple2 Bits_kctl Bits_dctl))
    )
    Bool
    (let
        (
            (pk (<pkg-state-KEM-<$<!dkeyl!><!kctl!><!kencr!><!pkeyl!><!skeyl!>$>-pk> (<game-ModularPkeCcaGame-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-pkgstate-KEM> old-state-right)))
            (sk (<pkg-state-KEM-<$<!dkeyl!><!kctl!><!kencr!><!pkeyl!><!skeyl!>$>-sk> (<game-ModularPkeCcaGame-<$<!pkeyl!><!skeyl!><!ptl!><!dkeyl!><!kctl!><!dctl!><!kgenr!><!kencr!>$>-pkgstate-KEM> old-state-right)))
        )
        (=>
            (not (is-mk-none pk))
            (forall 
                (
                    (r Bits_kencr)
                )
                (let
                    (
                        (k (el2-1 (<<func-kem_encaps>> r (maybe-get pk))))
                        (ek (el2-2 (<<func-kem_encaps>> r (maybe-get pk))))
                    )
                    (= k (<<func-kem_decaps>> (maybe-get sk) ek))
                )
            )
        )
    )
)
