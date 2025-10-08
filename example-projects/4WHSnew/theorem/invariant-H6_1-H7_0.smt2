;; Main idea of this invariant proof
;; If ctr are equal in both games and they use the same randomness, then both games
;;    - produce the same output
;;    - abort iff the other aborts
;;    - have same ctr afterwards
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Randomness mapping
;;
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
   (= id-0 2)
   (= id-1 3)))

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
   (or
    (and ; Nonces
     (= id-0 2)
     (= id-1 3))
    (and ; kmac
     (= id-0 1)
     (= id-1 2)))))

(define-fun <relation-lemma-randomness-H6_1-H7_0-Send2>
    ((H61-old <GameState_H6_<$<!n!>$>>)
     (H70-old <GameState_H7_<$<!n!>$>>)
     (H61-return <OracleReturn_H6_<$<!n!>$>_Game_noprfkey_<$<!n!>$>_Send2>)
     (H70-return <OracleReturn_H7_<$<!n!>$>_Game_noprfkey_<$<!n!>$>_Send2>)
     (ctr Int) (msg Bits_256))
  Bool
  (and (= (__sample-rand-H6_1-Bits_256 2 (<game-H6-<$<!n!>$>-rand-2> H61-old))
          (__sample-rand-H7_0-Bits_256 3 (<game-H7-<$<!n!>$>-rand-3> H70-old)))
       (= (__sample-rand-H6_1-Bits_256 1 (<game-H6-<$<!n!>$>-rand-1> H61-old))
          (__sample-rand-H7_0-Bits_256 2 (<game-H7-<$<!n!>$>-rand-2> H70-old)))))



(define-fun randomness-mapping-Send3
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  ;; There is no randomness used in this oracle.
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 1)
   (= id-1 2)))

(define-fun randomness-mapping-Send4
    ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
      (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
      (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
      (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
      (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 id-1 1)))


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
   (= scr-0 base-ctr-0)
   (or
    (= id-0 id-1 1)
    (and
     (= id-0 3)
     (= id-1 4)))))

(define-fun <relation-lemma-randomness-H6_1-H7_0-Test>
    ((H61-old <GameState_H6_<$<!n!>$>>)
     (H70-old <GameState_H7_<$<!n!>$>>)
     (H61_return <OracleReturn_H6_<$<!n!>$>_Game_noprfkey_<$<!n!>$>_Test>)
     (H70_return <OracleReturn_H7_<$<!n!>$>_Game_noprfkey_<$<!n!>$>_Test>)
     (ctr Int))
  Bool
  (and (= (__sample-rand-H6_1-Bits_256 1 (<game-H6-<$<!n!>$>-rand-1> H61-old))
          (__sample-rand-H7_0-Bits_256 1 (<game-H7-<$<!n!>$>-rand-1> H70-old)))
       (= (__sample-rand-H6_1-Bits_256 3 (<game-H6-<$<!n!>$>-rand-3> H61-old))
          (__sample-rand-H7_0-Bits_256 4 (<game-H7-<$<!n!>$>-rand-4> H70-old)))))


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
   (= id-0     0)   ; This is the 0th sampling in KX   and samples the random key in NewKey.
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
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
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
  ;; There is no randomness used in this oracle.
  false
  )


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                                      ;
;; Invariant --- note that the invariant needs to be game-global and not per oracle,                    ;
;;               so that induction over the oracle calls remains meaningful.                            ;
;;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun no-overwriting-prf ((prf <PackageState_PRF_<$<!n!>$>>))
  Bool
  (let ((kid (<pkg-state-PRF-<$<!n!>$>-kid_> prf))
        (LTK (<pkg-state-PRF-<$<!n!>$>-LTK> prf))
        (H (<pkg-state-PRF-<$<!n!>$>-H> prf)))
    (forall ((i Int))
            (and
             (=> (= (select H i) (as mk-none (Maybe Bool)))
                 (= (select LTK i) (as mk-none (Maybe Bits_256))))
             (=> (= (select LTK i) (as mk-none (Maybe Bits_256)))
                 (= (select H i) (as mk-none (Maybe Bool))))
             (=> (> i kid)
                 (and (= (select H i)
                         (as mk-none (Maybe Bool)))
                      (= (select LTK i)
                         (as mk-none (Maybe Bits_256)))))))))


(define-fun key-not-computed-unless-test-or-reveal
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (revtest (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool)))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (H (Array Int (Maybe Bool))))
  Bool
  (and
   ;; mac keys are computed before output keys
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_256)
            (nr Bits_256))
           (=> (not (= (select prf (mk-tuple6 kid U V ni nr true))
                       (as mk-none (Maybe Bits_256))))
               (not (= (select prf (mk-tuple6 kid U V ni nr false))
                       (as mk-none (Maybe Bits_256))))))

   ;; output keys are only computed when revtesting
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_256)
            (nr Bits_256)
            (kmac-prime Bits_256))
           (and
            ;; entry in PRF table => entry in revtest
            (=> (not (= (select prf (mk-tuple6 kid U V ni nr true))
                        (as mk-none (Maybe Bits_256))))
                (let ((kmac (select prf (mk-tuple6 kid U V ni nr false))))
                  (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                    (not (= (select revtest (mk-tuple5 U V ni nr tau))
                            (as mk-none (Maybe Bool)))))))

            ;; revtest none => prf none
            (=> (let ((tau (<<func-mac>> kmac-prime nr 2)))
                  (= (select revtest (mk-tuple5 U V ni nr tau))
                     (as mk-none (Maybe Bool))))
                (=> (= (select prf (mk-tuple6 kid U V ni nr false))
                       (mk-some kmac-prime))
                    (= (select prf (mk-tuple6 kid U V ni nr true))
                       (as mk-none (Maybe Bits_256)))))))))


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
                              (ite (= mess 0)
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256)))
                                        (= acc (as mk-none (Maybe Bool))))
                                   (and (ite (= mess 1) (= acc (as mk-none (Maybe Bool))) (not (= acc (as mk-none (Maybe Bool)))))
                                        (=> (> mess 0)
                                               (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                                    (not (= kmac (as mk-none (Maybe Bits_256))))
                                                    (not (= ni (as mk-none (Maybe Bits_256))))
                                                    (not (= nr (as mk-none (Maybe Bits_256))))))))
                              (ite (= mess 0)
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256)))
                                        (= acc (as mk-none (Maybe Bool))))
                                   (ite (= mess 1)
                                        (and (not (= ni (as mk-none (Maybe Bits_256))))
                                             (= acc (as mk-none (Maybe Bool)))
                                             (= nr kmac (as mk-none (Maybe Bits_256)))
                                             (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                        (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                             (not (= kmac (as mk-none (Maybe Bits_256))))
                                             (not (= ni (as mk-none (Maybe Bits_256))))
                                             (not (= nr (as mk-none (Maybe Bits_256)))))))))))))))


(define-fun other-stuff-not-initialized-early
    ((State1 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Fresh1 (Array Int (Maybe Bool)))
     (Keys1 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Bits_256))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select State1 ctr)))
              (=> (not (= state none))
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
                    (and (not (is-mk-none (select Fresh1 ctr)))
                         (ite u
                              (ite (> mess 0)
                                   (and (ite (= mess 1) (= acc (as mk-none (Maybe Bool))) (not (= acc (as mk-none (Maybe Bool)))))
                                        (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                        (ite (= (select Fresh1 ctr) (mk-some true))
                                             (not (is-mk-none (select Keys1 (mk-tuple5 kid V U (maybe-get ni) (maybe-get nr)))))
                                             (not (is-mk-none kmac)))
                                        (not (= ni (as mk-none (Maybe Bits_256))))
                                        (not (= nr (as mk-none (Maybe Bits_256)))))
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256)))))
                              (ite (= mess 0)
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_256)))
                                        (= acc (as mk-none (Maybe Bool))))
                                   (ite (= mess 1)
                                        (and (not (= ni (as mk-none (Maybe Bits_256))))
                                             (= nr kmac (as mk-none (Maybe Bits_256)))
                                             (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))
                                             (= acc (as mk-none (Maybe Bool))))
                                        (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                                             (ite (= (select Fresh1 ctr) (mk-some true))
                                                  (not (is-mk-none (select Keys1 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr)))))
                                                  (not (is-mk-none kmac)))
                                             (not (= ni (as mk-none (Maybe Bits_256))))
                                             (not (= nr (as mk-none (Maybe Bits_256)))))))))))))))


(define-fun state-equality
    ((State0 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                        (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (State1 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                        (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                        (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Fresh1 (Array Int (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (and
             (= (is-mk-none (select State1 ctr))
                (is-mk-none (select State0 ctr)))
             (let ((state0 (select State0 ctr)))
               (=> (not (= state0 none))
                   (let  ((U    (el11-1  (maybe-get state0)))
                          (u    (el11-2  (maybe-get state0)))
                          (V    (el11-3  (maybe-get state0)))
                          (ltk  (el11-4  (maybe-get state0)))
                          (acc  (el11-5  (maybe-get state0)))
                          (k    (el11-6  (maybe-get state0)))
                          (ni   (el11-7  (maybe-get state0)))
                          (nr   (el11-8  (maybe-get state0)))
                          (kmac (el11-9  (maybe-get state0)))
                          (sid  (el11-10 (maybe-get state0)))
                          (mess (el11-11 (maybe-get state0))))
                     (ite (= (select Fresh1 ctr) (mk-some true)) 
                          (= (select State1 ctr)
                             (mk-some (mk-tuple11 U u V ltk acc k ni nr (as mk-none (Maybe Bits_256)) sid mess)))
                          (= (select State1 ctr) state0)))))))))


(define-fun prf-equality
    ((Prf0 (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (Prf1 (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (Keys1 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Bits_256))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (and
           (= (select Prf0 (mk-tuple6 kid U V ni nr true))
              (select Prf1 (mk-tuple6 kid U V ni nr true)))
           (= (select Prf0 (mk-tuple6 kid U V ni nr false))
              (select Keys1 (mk-tuple5 kid U V ni nr))))))

  
     
(define-fun all-sessions-have-valid-keys
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (ltk (Array Int (Maybe Bits_256))))
  Bool
    (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
      (forall ((ctr Int))
              (let ((state (select state ctr)))
                (=> (not (= state none))
                    (let  ((kid  (el11-4  (maybe-get state))))
                      (not (= (select ltk kid) (as mk-none (Maybe Bits_256))))))))))



(define-fun kmac-sampled-consistently
    ((prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (keys (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Bits_256))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (and 
          (=> (= (select prf (mk-tuple6 kid U V ni nr false))
                 (as mk-none (Maybe Bits_256)))
              (= (select keys (mk-tuple5 kid U V ni nr))
                 (as mk-none (Maybe Bits_256))))
          (=> (= (select keys (mk-tuple5 kid U V ni nr))
                 (as mk-none (Maybe Bits_256)))
              (= (select prf (mk-tuple6 kid U V ni nr false))
                 (as mk-none (Maybe Bits_256)))))))


(define-fun kmac-consistent-in-state-and-mac
    ((State0 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (State1 (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Fresh1 (Array Int (Maybe Bool)))
     (Keys1 (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Bits_256))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State0 ctr)))
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
                  (=> (not (= kmac (as mk-none (Maybe Bits_256))))
                      (ite (= (select Fresh1 ctr) (mk-some true))
                           (= kmac (select Keys1 (mk-tuple5 kid (ite u V U) (ite u U V) (maybe-get ni) (maybe-get nr))))
                           (= kmac (el11-9 (maybe-get (select State1 ctr))))
                           )))))))
  
(define-fun freshness-is-known
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (fresh (Array Int (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (not (= (select fresh ctr) (as mk-none (Maybe Bool)))))))))

(define-fun freshness-and-honesty-matches
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (fresh (Array Int (Maybe Bool)))
     (honest (Array Int (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (is-mk-none state))
                  (let ((kid (el11-4  (maybe-get state))))
                    (= (select fresh ctr)
                       (select honest kid))))))))


(define-fun prf-package-set-consistently
    ((ltk (Array Int (Maybe Bits_256)))
     (hon (Array Int (Maybe Bool)))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (and 
   (forall ((kid Int))
           (and
            (=> (= (select ltk kid) (as mk-none (Maybe Bits_256)))
                (= (select hon kid) (as mk-none (Maybe Bool))))
            (=> (= (select hon kid) (as mk-none (Maybe Bool)))
                (= (select ltk kid) (as mk-none (Maybe Bits_256))))))
   (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256) (flag Bool))
           (=> (not (= (select prf (mk-tuple6 kid U V ni nr flag))
                       (as mk-none (Maybe Bits_256))))
               (not (= (select ltk kid)
                       (as mk-none (Maybe Bits_256))))))))
  

(define-fun mac-values-stored
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (fresh (Array Int (Maybe Bool)))
     (values (Array (Tuple2 (Tuple5 Int Int Int Bits_256 Bits_256) (Tuple2 Bits_256 Int)) (Maybe Bits_256))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                          (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                          (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (and (not (= state none))
                       (= (select fresh ctr) (mk-some true)))
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
                    (let ((handle (mk-tuple5 kid (ite u V U) (ite u U V) (maybe-get ni) (maybe-get nr))))
                      (ite (< 0 mess)
                           (not (= (select values (mk-tuple2 handle (mk-tuple2 (maybe-get nr) 2)))
                                   (as mk-none (Maybe Bits_256))))
                           true
                           ))))))))

(define-fun revtesteval-populated
    ((revtesteval (Array (Tuple5 Int Int Int Bits_256 Bits_256) (Maybe Int)))
     (H (Array Int (Maybe Bool)))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (let ((pos-prf (mk-tuple6 kid U V ni nr true))
                (pos-rev (mk-tuple5 kid U V ni nr)))
            (and
             (=> (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_256)))
                 (or (= (select H kid) (mk-some false))
                     (= (select revtesteval pos-rev)
                        (as mk-none (Maybe Int)))))
             (=> (= (select revtesteval pos-rev)
                    (as mk-none (Maybe Int)))
                 (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_256))))))))


(define-fun sid-is-wellformed
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
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
                         (kid  (el11-4  (maybe-get state)))
                         (acc  (el11-5  (maybe-get state)))
                         (k    (el11-6  (maybe-get state)))
                         (ni   (el11-7  (maybe-get state)))
                         (nr   (el11-8  (maybe-get state)))
                         (kmac (el11-9  (maybe-get state)))
                         (sid  (el11-10 (maybe-get state)))
                         (mess (el11-11 (maybe-get state))))
                    (=> (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
                        (let ((tau (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2)))
                          (= (mk-tuple5 (ite u V U) (ite u U V)
                                        (maybe-get ni) (maybe-get nr) tau)
                             (maybe-get sid))))))))))


(define-fun invariant
    ((state-H61  <GameState_H6_<$<!n!>$>>)
     (state-H70  <GameState_H7_<$<!n!>$>>))
  Bool
  (let ((nonces-H61 (<game-H6-<$<!n!>$>-pkgstate-Nonces> state-H61))
        (nonces-H70 (<game-H7-<$<!n!>$>-pkgstate-Nonces>  state-H70))
        (game-H61 (<game-H6-<$<!n!>$>-pkgstate-Game_noprfkey> state-H61))
        (game-H70 (<game-H7-<$<!n!>$>-pkgstate-Game_noprfkey>  state-H70))
        (prf-H61 (<game-H6-<$<!n!>$>-pkgstate-PRF> state-H61))
        (prf-H70 (<game-H7-<$<!n!>$>-pkgstate-PRF>  state-H70))
        (mac-H70 (<game-H7-<$<!n!>$>-pkgstate-MAC>  state-H70)))
    (let ((ctr0 (<pkg-state-Game_noprfkey-<$<!n!>$>-ctr_> game-H61))
          (ctr1 (<pkg-state-Game_noprfkey-<$<!n!>$>-ctr_> game-H70))
          (State0 (<pkg-state-Game_noprfkey-<$<!n!>$>-State> game-H61))
          (State1 (<pkg-state-Game_noprfkey-<$<!n!>$>-State> game-H70))
          (RevTested0 (<pkg-state-Game_noprfkey-<$<!n!>$>-RevTested> game-H61))
          (RevTested1 (<pkg-state-Game_noprfkey-<$<!n!>$>-RevTested> game-H70))
          (RevTestEval0 (<pkg-state-Game_noprfkey-<$<!n!>$>-RevTestEval> game-H61))
          (RevTestEval1 (<pkg-state-Game_noprfkey-<$<!n!>$>-RevTestEval> game-H70))
          (Fresh0 (<pkg-state-Game_noprfkey-<$<!n!>$>-Fresh> game-H61))
          (Fresh1 (<pkg-state-Game_noprfkey-<$<!n!>$>-Fresh> game-H70))
          (First0 (<pkg-state-Game_noprfkey-<$<!n!>$>-First> game-H61))
          (First1 (<pkg-state-Game_noprfkey-<$<!n!>$>-First> game-H70))
          (Second0 (<pkg-state-Game_noprfkey-<$<!n!>$>-Second> game-H61))
          (Second1 (<pkg-state-Game_noprfkey-<$<!n!>$>-Second> game-H70))
          (Nonces0 (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H61))
          (Nonces1 (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H70))
          (Ltk0 (<pkg-state-PRF-<$<!n!>$>-LTK> prf-H61))
          (Ltk1 (<pkg-state-PRF-<$<!n!>$>-LTK> prf-H70))
          (Prf0 (<pkg-state-PRF-<$<!n!>$>-PRF> prf-H61))
          (Prf1 (<pkg-state-PRF-<$<!n!>$>-PRF> prf-H70))
          (H0 (<pkg-state-PRF-<$<!n!>$>-H> prf-H61))
          (H1 (<pkg-state-PRF-<$<!n!>$>-H> prf-H70))
          (Keys1 (<pkg-state-MAC-<$<!n!>$>-Keys> mac-H70))
          (Values1 (<pkg-state-MAC-<$<!n!>$>-Values> mac-H70))
          )
      (and (= Nonces0 Nonces1)
           (= Ltk0 Ltk1)
           (= H0 H1)
           (= (<pkg-state-PRF-<$<!n!>$>-kid_> prf-H61)
              (<pkg-state-PRF-<$<!n!>$>-kid_> prf-H70))
           (= ctr0 ctr1)
           (= RevTested0 RevTested1)
           (= RevTestEval0 RevTestEval1)
           (= Fresh0 Fresh1)
           (= First0 First1)
           (= Second0 Second1)

           (state-equality State0 State1 Fresh1)
           (prf-equality Prf0 Prf1 Keys1)

           (no-overwriting-prf prf-H61)
           
           (freshness-and-honesty-matches State0 Fresh0 H0)
           (freshness-and-honesty-matches State1 Fresh1 H1)
           (freshness-is-known State0 Fresh0)
           (freshness-is-known State1 Fresh1)
           (stuff-not-initialized-early State0)
           (other-stuff-not-initialized-early State1 Fresh1 Keys1)
           (kmac-sampled-consistently Prf0 Keys1)
           (kmac-consistent-in-state-and-mac State0 State1 Fresh1 Keys1)
           (prf-package-set-consistently Ltk0 H0 Prf0)
           (prf-package-set-consistently Ltk1 H1 Prf1)
           (all-sessions-have-valid-keys State0 Ltk0)
           (revtesteval-populated RevTestEval0 H0 Prf0)
           (revtesteval-populated RevTestEval1 H1 Prf1)
           (sid-is-wellformed State0 Prf0)))))
