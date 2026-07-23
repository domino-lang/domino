(define-state-relation invariant
    (left right)
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

(define-fun kem-correctness
    (
        (pk (Maybe Bits_pkeyl))
        (sk (Maybe Bits_skeyl))
    )
    Bool
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

(define-lemma <relation-lemma-kem-correctness-Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-PKENC>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (m0 Bits_ptl)
        (m1 Bits_ptl)
    )
    (kem-correctness old-state-right.KEM.pk old-state-right.KEM.sk)
)

(define-lemma <relation-lemma-kem-correctness-Game_MON_CCA_PKE-Game_MOD_CCA_PKE_Real_KEM-PKDEC>
    (
        old-state-left
        old-state-right
        return-left
        return-right
        (ek_ctxt (Tuple2 Bits_kctl Bits_dctl))
    )
    (kem-correctness old-state-right.KEM.pk old-state-right.KEM.sk)
)
