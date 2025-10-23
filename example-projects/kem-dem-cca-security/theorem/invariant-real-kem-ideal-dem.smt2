(define-fun randomness-mapping-PKGEN
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_KemScheme" "KEM_GEN" "kem_gen"))
        )
    )
)

(define-fun randomness-mapping-PKENC
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    (or
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
        )
        (and
            (= sample-ctr-monolithic_pke_cca_game sample-ctr-old-monolithic_pke_cca_game)
            (= sample-ctr-modular_pke_cca_game_with_real_kem sample-ctr-old-modular_pke_cca_game_with_real_kem)
            (= sample-id-monolithic_pke_cca_game (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
            (= sample-id-modular_pke_cca_game_with_real_kem (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
        )
    )
)

(define-fun randomness-mapping-PKDEC
    ( 
        (sample-ctr-old-monolithic_pke_cca_game Int)
        (sample-ctr-old-modular_pke_cca_game_with_real_kem Int)
        (sample-id-monolithic_pke_cca_game SampleId)
        (sample-id-modular_pke_cca_game_with_real_kem SampleId)
        (sample-ctr-monolithic_pke_cca_game Int)
        (sample-ctr-modular_pke_cca_game_with_real_kem Int)
    )
    Bool
    false
)

(define-fun invariant
    (
        (state-left <GameState_MonolithicPkeCcaGame>) ; left
        (state-right <GameState_ModularPkeCcaGame>) ; right
    )
    Bool
    (let
        (
            (left_pk (<pkg-state-MON_CCA-pk> (<game-MonolithicPkeCcaGame-pkgstate-pkg_MON_CCA> state-left)))
            (left_sk (<pkg-state-MON_CCA-sk> (<game-MonolithicPkeCcaGame-pkgstate-pkg_MON_CCA> state-left)))
            (right_pk_mod_cca (<pkg-state-MOD_CCA-pk> (<game-ModularPkeCcaGame-pkgstate-pkg_MOD_CCA> state-right)))
            (right_pk_kem (<pkg-state-KEM-pk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> state-right)))
            (left_c (<pkg-state-MON_CCA-c> (<game-MonolithicPkeCcaGame-pkgstate-pkg_MON_CCA> state-left)))
            (right_c (<pkg-state-MOD_CCA-c> (<game-ModularPkeCcaGame-pkgstate-pkg_MOD_CCA> state-right)))
            (right_kem_ek (<pkg-state-KEM-ek> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> state-right)))
            (right_mod_cca_ek (<pkg-state-MOD_CCA-ek> (<game-ModularPkeCcaGame-pkgstate-pkg_MOD_CCA> state-right)))
            (right_dem_c (<pkg-state-MOD_CCA-em> (<game-ModularPkeCcaGame-pkgstate-pkg_MOD_CCA> state-right)))
            (right_key_k (<pkg-state-Key-k> (<game-ModularPkeCcaGame-pkgstate-pkg_Key> state-right)))
            (right_sk (<pkg-state-KEM-sk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> state-right)))
            (right_encaps_randomness (<pkg-state-KEM-encaps_randomness> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> state-right)))
            (right_T (<pkg-state-DEM-T> (<game-ModularPkeCcaGame-pkgstate-pkg_DEM> state-right)))
        )
        (and
            (= left_pk right_pk_mod_cca right_pk_kem) ; left_pk = right_pk
            (= ((_ is mk-none) left_pk) ((_ is mk-none) left_sk) ((_ is mk-none) right_pk_mod_cca) ((_ is mk-none) right_pk_kem) ((_ is mk-none) right_sk)) ; left_pk = None iff right_pk = None
            (= left_c right_c) ; left_challenge_ciphertext = right_challenge_ciphertext
            (= ((_ is mk-none) right_encaps_randomness) ((_ is mk-none) left_c) ((_ is mk-none) right_c) ((_ is mk-none) right_kem_ek) ((_ is mk-none) right_mod_cca_ek) ((_ is mk-none) right_dem_c) ((_ is mk-none) right_key_k)) ; left_challenge_ciphertext = None iff right_challenge_ciphertext = None iff right_encapsulation_challenge = None iff right_dem_challenge = None iff right_key_k = None
            (= left_sk right_sk) ; left_sk = right_sk
            (= right_mod_cca_ek right_kem_ek) ; right encapsulated keys
            (=> ((_ is mk-none) right_pk_kem) ((_ is mk-none) right_c)) ; if PKGEN is not called, PKENC can not be called
            (=>
                (not ((_ is mk-none) right_c))
                (= (maybe-get right_c) (mk-tuple2 (maybe-get right_mod_cca_ek) (maybe-get right_dem_c)))
            )
            (=>
                (not ((_ is mk-none) right_key_k))
                (and
                    (= (maybe-get right_key_k) (el2-1 (<<func-kem_encaps>> (maybe-get right_encaps_randomness) (maybe-get right_pk_kem))))
                    (= (maybe-get right_kem_ek) (el2-2 (<<func-kem_encaps>> (maybe-get right_encaps_randomness) (maybe-get right_pk_kem))))
                )
            )
            (forall 
                (
                    (x Bits_*)
                )

                    (and 
                        (=> 
                            ((_ is mk-none) right_c)
                            ((_ is mk-none) (select right_T x))
                        )
                        (=> 
                            (not ((_ is mk-none) right_c))
                            (= (= x (maybe-get right_dem_c)) (not ((_ is mk-none) (select right_T x))))
                        )
                    )
            )
        )
    )
)

(define-fun <relation-lemma-kem-correctness-monolithic_pke_cca_ideal_game-modular_pke_cca_game_with_real_kem_and_ideal_dem-PKDEC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame>)
        (old-state-right <GameState_ModularPkeCcaGame>)
        (return-left <OracleReturn_MonolithicPkeCcaGame_MON_CCA_PKDEC>)
        (return-right <OracleReturn_ModularPkeCcaGame_MOD_CCA_PKDEC>)
        (ek_ctxt (Tuple2 Bits_400 Bits_*))
    )
    Bool
    (let
        (
            (pk (<pkg-state-KEM-pk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> old-state-right)))
            (sk (<pkg-state-KEM-sk> (<game-ModularPkeCcaGame-pkgstate-pkg_KEM> old-state-right)))
        )
        (=>
            (not ((_ is mk-none) pk))
            (forall 
                (
                    (r Bits_3000)
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

(define-fun <relation-lemma-rand-is-eq-monolithic_pke_cca_ideal_game-modular_pke_cca_game_with_real_kem_and_ideal_dem-PKENC>
    (
        (old-state-left <GameState_MonolithicPkeCcaGame>)
        (old-state-right <GameState_ModularPkeCcaGame>)
        (return-left <OracleReturn_MonolithicPkeCcaGame_MON_CCA_PKENC>)
        (return-right <OracleReturn_ModularPkeCcaGame_MOD_CCA_PKENC>)
        (m Bits_*)
    )
    Bool 
    (let 
        (
            (dem_mapping_id (sample-id "pkg_DemScheme" "DEM_ENC" "dem_enc"))
            (kem_mapping_id (sample-id "pkg_KemScheme" "KEM_ENCAPS" "kem_encaps"))
        )
        (and
            (rand-is-eq dem_mapping_id dem_mapping_id (<game-MonolithicPkeCcaGame-rand-pkg_DemScheme-DEM_ENC-dem_enc> old-state-left) (<game-ModularPkeCcaGame-rand-pkg_DemScheme-DEM_ENC-dem_enc> old-state-right))
            (rand-is-eq kem_mapping_id kem_mapping_id (<game-MonolithicPkeCcaGame-rand-pkg_KemScheme-KEM_ENCAPS-kem_encaps> old-state-left) (<game-ModularPkeCcaGame-rand-pkg_KemScheme-KEM_ENCAPS-kem_encaps> old-state-right))
        )
    )
)