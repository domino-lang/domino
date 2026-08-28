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
        (=> 
            (not (is-mk-none right.KEM.pk))
            (and 
                (= (maybe-get right.KEM.pk) (el2-1 (<<func-kem_gen>> right.Scheme_KEM.ghost)))
                (= (maybe-get right.KEM.sk) (el2-2 (<<func-kem_gen>> right.Scheme_KEM.ghost)))
            )
            ; the following also works; no need for ghost but exists :D
            ;(exists 
            ;    (
            ;        (r Bits_kgenr)
            ;    )
            ;    (and 
            ;        (= (maybe-get right.KEM.pk) (el2-1 (<<func-kem_gen>> r)))
            ;        (= (maybe-get right.KEM.sk) (el2-2 (<<func-kem_gen>> r)))
            ;    )
            ;)
        )
    )
)

; kem correctness property
(assert 
    (forall 
        (
            (r Bits_kgenr)
        )
        (let 
            (
                (pk (el2-1 (<<func-kem_gen>> r)))
                (sk (el2-2 (<<func-kem_gen>> r)))
            )
            (forall 
                (
                    (r Bits_kencr)
                )
                (let
                    (
                        (k (el2-1 (<<func-kem_encaps>> r pk)))
                        (ek (el2-2 (<<func-kem_encaps>> r pk)))
                    )
                    (= k (<<func-kem_decaps>> sk ek))
                )
            )
        )
    )
)