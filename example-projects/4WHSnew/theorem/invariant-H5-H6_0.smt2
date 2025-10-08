; Main idea of this invariant proof
; If ctr are equal in both games and they use the same randomness, then both games
;    - produce the same output
;    - abort iff the other aborts
;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-Send1
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      0)  ; This is the 2nd sampling in KX and samples ni.
    (= id-1      2)  ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
    ))

(define-fun randomness-mapping-Send2
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0     0)   ; This is the 3rd sampling in KX and samples nr.
    (= id-1     2)   ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
  ))

(define-fun randomness-mapping-Send3
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)

(define-fun randomness-mapping-Send4
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)

(define-fun randomness-mapping-Send5
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)

(define-fun randomness-mapping-Reveal
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)

(define-fun randomness-mapping-Test
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= id-0     2)   ; This is the 1st sampling in KX   and samples the random key in Test.
    (= id-1     3)   ; This is the 1st sampling in H1_0 and samples the random key in Test.
))

(define-fun randomness-mapping-NewKey
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0     1)   ; This is the 0th sampling in KX   and samples the random key in NewKey.
    (= id-1     0)   ; This is the 0th sampling in H1_0 and samples the random key in NewKey.
  ))

(define-fun randomness-mapping-NewSession
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)

(define-fun randomness-mapping-SameKey
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)
(define-fun randomness-mapping-AtMost
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)
(define-fun randomness-mapping-AtLeast
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
                     ; There is no randomness used in this oracle.
                     false
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;                                                                                                      ;
; Invariant --- note that the invariant needs to be game-global and not per oracle,                    ;
;               so that induction over the oracle calls remains meaningful.                            ;
;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun state-equality
    ((state-H5 (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (state-H6 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (prf-H6 (Array Int (Maybe Bits_256)))
     (hon-H6 (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (and (= (is-mk-none (select state-H5 ctr))
                  (is-mk-none (select state-H6 ctr)))
               (let ((state (select state-H6 ctr)))
                 (=> (not (is-mk-none state))
                     (let  ((U    (el11-1  (maybe-get state)))
                            (u    (el11-2  (maybe-get state)))
                            (V    (el11-3  (maybe-get state)))
                            (kid  (el11-4  (maybe-get state)))
                            (acc  (el11-5  (maybe-get state)))
                            (k    (el11-6  (maybe-get state)))
                            (ni   (el11-7  (maybe-get state)))
                            (nr   (el11-8  (maybe-get state)))
                            (kmac (el11-9  (maybe-get state)))
                            (sid  (el11-10 (maybe-get state)))
                            (mess (el11-11 (maybe-get state))))
                       (let ((ltk (select prf-H6 kid))
                             (hon (select hon-H6 kid)))
                         (and (= k (as mk-none (Maybe Bits_256)))
                              (not (= ltk (as mk-none (Maybe Bits_256))))
                              (not (= hon (as mk-none (Maybe Bool))))
                              (= (select state-H5 ctr)
                                 (mk-some (mk-tuple11 U u V (maybe-get ltk) acc (as mk-none (Maybe Bits_256))
                                                      ni nr kmac sid mess)))))))))))


(define-fun no-overwriting ((prf <PackageState_PRF_<$<!n!>$>>))
  Bool
  (let ((kid (<pkg-state-PRF-<$<!n!>$>-kid_> prf))
        (LTK (<pkg-state-PRF-<$<!n!>$>-LTK> prf))
        (H (<pkg-state-PRF-<$<!n!>$>-H> prf)))
    (forall ((i Int))
            (=> (> i kid)
                (and (is-mk-none (select LTK i))
                     (is-mk-none (select H i)))))))


(define-fun ltk-and-h-set-equally ((prf <PackageState_PRF_<$<!n!>$>>))
  Bool
  (let ((LTK (<pkg-state-PRF-<$<!n!>$>-LTK> prf))
        (H (<pkg-state-PRF-<$<!n!>$>-H> prf)))
    (forall ((i Int))
            (= (is-mk-none (select LTK i))
               (is-mk-none (select H i))))))

;; ni and nr are not none when accepted!

(define-fun nonces-are-not-none 
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (ltk  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (=> (= acc (mk-some true))
                        (and (not (= ni (as mk-none (Maybe Bits_256))))
                             (not (= nr (as mk-none (Maybe Bits_256))))))))))))


(define-fun stuff-not-initialized-early
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let  ((U    (el11-1  (maybe-get state)))
                         (u    (el11-2  (maybe-get state)))
                         (V    (el11-3  (maybe-get state)))
                         (ltk  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (and (ite u
                              (ite (> mess 0)
                                   (and (not (= kmac (as mk-none (Maybe Bits_256))))
                                        (not (= ni (as mk-none (Maybe Bits_256))))
                                        (not (= nr (as mk-none (Maybe Bits_256)))))
                                   (= ni nr kmac (as mk-none (Maybe Bits_256))))
                              (ite (= mess 0)
                                   (= ni nr kmac (as mk-none (Maybe Bits_256)))
                                   (ite (= mess 1)
                                        (and (not (= ni (as mk-none (Maybe Bits_256))))
                                             (= nr kmac (as mk-none (Maybe Bits_256))))
                                        (and (not (= kmac (as mk-none (Maybe Bits_256))))
                                             (not (= ni (as mk-none (Maybe Bits_256))))
                                             (not (= nr (as mk-none (Maybe Bits_256)))))))))))))))


(define-fun invariant
  ((state-H5  <GameState_H5_<$<!n!>$>>)
   (state-H6  <GameState_H6_<$<!n!>$>>))
  Bool
  (let ((nonces-H5 (<game-H5-<$<!n!>$>-pkgstate-Nonces>          state-H5))
        (nonces-H6 (<game-H6-<$<!n!>$>-pkgstate-Nonces> state-H6))
        (game-H5 (<game-H5-<$<!n!>$>-pkgstate-Game_nokey>             state-H5))
        (game-H6 (<game-H6-<$<!n!>$>-pkgstate-Game_noprfkey> state-H6))
        (prf-H6 (<game-H6-<$<!n!>$>-pkgstate-PRF> state-H6)))
    (and (= (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H5)
            (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-LTK> game-H5)
            (<pkg-state-PRF-<$<!n!>$>-LTK>              prf-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-ctr_>    game-H5)
            (<pkg-state-Game_noprfkey-<$<!n!>$>-ctr_> game-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-H> game-H5)
            (<pkg-state-PRF-<$<!n!>$>-H>              prf-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-kid_> game-H5)
            (<pkg-state-PRF-<$<!n!>$>-kid_>              prf-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-RevTested>    game-H5)
            (<pkg-state-Game_noprfkey-<$<!n!>$>-RevTested> game-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-Fresh>    game-H5)
            (<pkg-state-Game_noprfkey-<$<!n!>$>-Fresh> game-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-First>    game-H5)
            (<pkg-state-Game_noprfkey-<$<!n!>$>-First> game-H6))
         (= (<pkg-state-Game_nokey-<$<!n!>$>-Second>    game-H5)
            (<pkg-state-Game_noprfkey-<$<!n!>$>-Second> game-H6))

         (no-overwriting prf-H6)
         (ltk-and-h-set-equally prf-H6)

         (let ((state-H5 (<pkg-state-Game_nokey-<$<!n!>$>-State>    game-H5))
               (state-H6 (<pkg-state-Game_noprfkey-<$<!n!>$>-State> game-H6))
               (ltk-H6 (<pkg-state-PRF-<$<!n!>$>-LTK> prf-H6))
               (hon-H6 (<pkg-state-PRF-<$<!n!>$>-H> prf-H6)))
           (and
            (state-equality state-H5 state-H6 ltk-H6 hon-H6))))))
