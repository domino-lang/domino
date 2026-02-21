(define-fun no-ideal-values-for-dishonest-keys
    ((H (Array Int (Maybe Bool)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n)))
     (Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (= (select H kid) (mk-some false))
              (and
               (forall ((msg Bits_n) (tag Int))
                       (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                             (mk-tuple2 msg tag)))))
               (is-mk-none (select Keys (mk-tuple5 kid U V ni nr)))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))))


(define-fun revtesteval-empty
    ((RevTestEval (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (RevTested (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
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
                  (=> (not (= acc (mk-some true)))
                      (and (is-mk-none (select RevTestEval (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))))
                           (is-mk-none (select RevTested (maybe-get sid))))))))))

(define-fun revtesteval-populated
    ((revtesteval (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (H (Array Int (Maybe Bool)))
     (prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (let ((pos-prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                (pos-rev (mk-tuple5 kid U V ni nr)))
            (and
             (=> (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_n)))
                 (or (= (select H kid) (mk-some false))
                     (= (select revtesteval pos-rev)
                        (as mk-none (Maybe Int)))))
             (=> (= (select revtesteval pos-rev)
                    (as mk-none (Maybe Int)))
                 (= (select prf pos-prf)
                    (as mk-none (Maybe Bits_n))))))))


(define-fun revtesteval-matches-sometimes
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (revtesteval0 (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (revtesteval1 (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int))))
  Bool
  (and
   (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
           (=> (not (is-mk-none (select revtesteval1 (mk-tuple5 kid U V ni nr))))
               (= (select revtesteval1 (mk-tuple5 kid U V ni nr))
                  (select revtesteval0 (mk-tuple5 kid U V ni nr)))))))


(define-fun key-not-computed-unless-test-or-reveal
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (revtest (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool)))
     (prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (H (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (and
   ;; mac keys are computed before output keys
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_n)
            (nr Bits_n))
           (=> (not (= (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                       (as mk-none (Maybe Bits_n))))
               (ite (= (select H kid) (mk-some true))
                    (not (is-mk-none (select Keys (mk-tuple5 kid U V ni nr))))
                    (not (is-mk-none (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))))

   ;; output keys are only computed when revtesting
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_n)
            (nr Bits_n)
            (kmac-prime Bits_n))
           (and
            ;; entry in PRF table => entry in revtest
            (=> (not (is-mk-none (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))
                (let ((kmac (ite (= (select H kid) (mk-some true))
                                 (select Keys (mk-tuple5 kid U V ni nr))
                                 (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))
                  (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                    (not (= (select revtest (mk-tuple5 U V ni nr tau))
                            (as mk-none (Maybe Bool)))))))

            ;; revtest none => prf none
            (=> (let ((tau (<<func-mac>> kmac-prime nr 2)))
                  (= (select revtest (mk-tuple5 U V ni nr tau))
                     (as mk-none (Maybe Bool))))
                (=> (= (ite (= (select H kid) (mk-some true))
                            (select Keys (mk-tuple5 kid U V ni nr))
                            (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
                       (mk-some kmac-prime))
                    (= (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                       (as mk-none (Maybe Bits_n)))))))))

(define-fun key-not-computed-unless-reveal
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (revtest (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool)))
     (prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (H (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (and
   ;; mac keys are computed before output keys
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_n)
            (nr Bits_n))
           (=> (not (= (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                       (as mk-none (Maybe Bits_n))))
               (ite (= (select H kid) (mk-some true))
                    (not (is-mk-none (select Keys (mk-tuple5 kid U V ni nr))))
                    (not (is-mk-none (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))))

   ;; output keys are only computed when revealing
   (forall ((kid Int)
            (U Int)
            (V Int)
            (ni Bits_n)
            (nr Bits_n)
            (kmac-prime Bits_n))
           (and
            ;; entry in PRF table => false entry in revtest
            (=> (not (is-mk-none (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))
                (let ((kmac (ite (= (select H kid) (mk-some true))
                                 (select Keys (mk-tuple5 kid U V ni nr))
                                 (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))
                  (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                    (= (select revtest (mk-tuple5 U V ni nr tau))
                       (mk-some false)))))

            ;; revtest none => prf none
            (=> (let ((tau (<<func-mac>> kmac-prime nr 2)))
                  (= (select revtest (mk-tuple5 U V ni nr tau))
                     (as mk-none (Maybe Bool))))
                (=> (= (ite (= (select H kid) (mk-some true))
                            (select Keys (mk-tuple5 kid U V ni nr))
                            (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
                       (mk-some kmac-prime))
                    (= (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                       (as mk-none (Maybe Bits_n)))))
            ;; tested => prf none
            (=> (let ((tau (<<func-mac>> kmac-prime nr 2)))
                  (= (select revtest (mk-tuple5 U V ni nr tau))
                     (mk-some true)))
                (=> (= (ite (= (select H kid) (mk-some true))
                            (select Keys (mk-tuple5 kid U V ni nr))
                            (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
                       (mk-some kmac-prime))
                    (= (select prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                       (as mk-none (Maybe Bits_n)))))
            ))))

(define-fun prfeval-has-matching-session
    ((prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (revtesteval (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (revtesteval1 (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (revtest (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool)))
     (state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
    (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
            (let ((pos-prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))
                  (pos-rev (mk-tuple5 kid U V ni nr)))
              (and (=> (not (is-mk-none (select prf pos-prf)))
                       (not (is-mk-none (select revtesteval pos-rev))))
                   (=> (not (is-mk-none (select revtesteval pos-rev)))
                       (let ((ctr (maybe-get (select revtesteval pos-rev)))
                             (st (select state (maybe-get (select revtesteval pos-rev)))))
                         (and
                          (not (is-mk-none st))
                          (let  ((Up   (el11-1  (maybe-get st)))
                                 (u    (el11-2  (maybe-get st)))
                                 (Vp   (el11-3  (maybe-get st)))
                                 (kidp (el11-4  (maybe-get st)))
                                 (acc  (el11-5  (maybe-get st)))
                                 (k    (el11-6  (maybe-get st)))
                                 (nip  (el11-7  (maybe-get st)))
                                 (nrp  (el11-8  (maybe-get st)))
                                 (kmac (el11-9  (maybe-get st)))
                                 (sid  (el11-10 (maybe-get st)))
                                 (mess (el11-11 (maybe-get st))))
                            (and
                             (= acc (mk-some true))
                             (not (is-mk-none sid))
                             (= ni (maybe-get nip))
                             (= nr (maybe-get nrp))
                             (= U Up)
                             (= V Vp)
                             (= kid kidp)
                             (let ((kmac (ite (= (select Fresh ctr) (mk-some true))
                                              (select Keys (mk-tuple5 kid U V ni nr))
                                              kmac)))
                               (let ((tau (<<func-mac>> (maybe-get kmac) nr 2)))
                                 (= (mk-tuple5 U V ni nr tau)
                                    (maybe-get sid))))
                             (not (= (select revtest (maybe-get sid))
                                     (as mk-none (Maybe Bool))))))))))))))


(define-fun sid-matches
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr1 Int) (ctr2 Int))
          (let ((state1 (select state ctr1))
                (state2 (select state ctr2)))
            (=> (and (not (is-mk-none state1))
                     (not (is-mk-none state2)))
                (let ((U1    (el11-1 (maybe-get state1)))
                      (U2    (el11-1 (maybe-get state2)))
                      (u1    (el11-2 (maybe-get state1)))
                      (u2    (el11-2 (maybe-get state2)))
                      (V1    (el11-3 (maybe-get state1)))
                      (V2    (el11-3 (maybe-get state2)))
                      (kid1  (el11-4 (maybe-get state1)))
                      (kid2  (el11-4 (maybe-get state2)))
                      (ni1   (el11-7 (maybe-get state1)))
                      (ni2   (el11-7 (maybe-get state2)))
                      (nr1   (el11-8 (maybe-get state1)))
                      (nr2   (el11-8 (maybe-get state2)))
                      (kmac1 (el11-9 (maybe-get state1)))
                      (kmac2 (el11-9 (maybe-get state2)))
                      (sid1  (el11-10 (maybe-get state1)))
                      (sid2  (el11-10 (maybe-get state2))))
                  (and
                   (=> (and (not (is-mk-none sid1))
                            (not (is-mk-none sid2))
                            (= (mk-tuple5 kid1 U1 V1 ni1 nr1)
                               (mk-tuple5 kid2 U2 V2 ni2 nr2)))
                       (= sid1 sid2))
                   (=> (and (= (mk-tuple5 kid1 U1 V1 ni1 nr1)
                               (mk-tuple5 kid2 U2 V2 ni2 nr2))
                            (not (is-mk-none sid1)))
                       (= (select Fresh ctr1)
                          (select Fresh ctr2)))))))))



(define-fun sid-is-wellformed
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select state ctr)))
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
                  (=> (not (is-mk-none sid))
                      (let ((kmac (ite (= (select Fresh ctr) (mk-some true))
                                       (select Keys (mk-tuple5 kid U V
                                                               (maybe-get ni)
                                                               (maybe-get nr)))
                                       kmac)))
                        (and
                         (not (is-mk-none kmac))
                         (not (is-mk-none ni))
                         (not (is-mk-none nr))
                         (let ((tau (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2)))
                           (= (mk-tuple5 U V
                                         (maybe-get ni)
                                         (maybe-get nr)
                                         tau)
                              (maybe-get sid)))))))))))




;; Some consistency checks on the PRF package
;;
;; (i) LTK and H are written at the same locations
;; (ii) neither is written on larger indices than kid
;;
(define-fun no-overwriting-prf
    ((kid Int)
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (H (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n)))
     (Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((i Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n) (msg Bits_n) (tag Int))
          (and
           (= (> i kid)
              (is-mk-none (select H i))
              (is-mk-none (select Ltk i)))
           (=> (> i kid)
               (and (is-mk-none (select Keys (mk-tuple5 i U V ni nr)))
                    ;;(is-mk-none (select Values (mk-tuple2 (mk-tuple5 i U V ni nr) (mk-tuple2 msg tag))))
                    (is-mk-none (select Prf (mk-tuple2 i (mk-tuple5 U V ni nr true))))
                    (is-mk-none (select Prf (mk-tuple2 i (mk-tuple5 U V ni nr false)))))))))

(define-fun no-overwriting-game
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (fresh (Array Int (Maybe Bool)))
     (ctr Int))
  Bool
  (forall ((i Int))
          (= (> i ctr)
             (is-mk-none (select fresh i))
             (is-mk-none (select state i)))))




(define-fun kmac-and-tau-are-computed-correctly
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (honesty (Array Int (Maybe Bool)))
     (ltk (Array Int (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
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
                    (and
                     (not (= (select ltk kid) (as mk-none (Maybe Bits_n))))
                     (not (= (select honesty kid) (as mk-none (Maybe Bool))))
                     (and
                      (=> (and (not (= kmac (as mk-none (Maybe Bits_n))))
                               (= (select honesty kid) (mk-some false)))
                          (= kmac (mk-some (<<func-prf>> (maybe-get (select ltk kid))
                                                         (mk-tuple5 U V (maybe-get ni) (maybe-get nr) false)))))))))))))


(define-fun time-of-acceptance
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (acc  (el11-5  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (= (not (is-mk-none acc))
                     (ite u (> mess 1) (> mess 2))))))))

(define-fun stuff-not-initialized-early
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
    (forall ((ctr Int))
            (let ((state (select State ctr)))
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
                    (and (ite u
                              (ite (> mess 0)
                                   (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
                                        (ite (= (select Fresh ctr) (mk-some true))
                                             (not (is-mk-none (select Keys (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr)))))
                                             (not (is-mk-none kmac)))
                                        (not (= ni (as mk-none (Maybe Bits_n))))
                                        (not (= nr (as mk-none (Maybe Bits_n)))))
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_n)))))
                              (ite (= mess 0)
                                   (and (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))))
                                        (= ni nr kmac (as mk-none (Maybe Bits_n))))
                                   (ite (= mess 1)
                                        (and (not (= ni (as mk-none (Maybe Bits_n))))
                                             (= nr kmac (as mk-none (Maybe Bits_n)))
                                             (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
                                        (and (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
                                             (ite (= (select Fresh ctr) (mk-some true))
                                                  (not (is-mk-none (select Keys (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr)))))
                                                  (not (is-mk-none kmac)))
                                             (not (= ni (as mk-none (Maybe Bits_n))))
                                             (not (= nr (as mk-none (Maybe Bits_n)))))))))))))))



(define-fun own-nonce-is-unique
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (nonces (Array Bits_n (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
    (and
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
                     (ite u
                          (=> (not (= nr (as mk-none (Maybe Bits_n))))
                              (= (select nonces (maybe-get nr)) (mk-some true)))
                          (=> (not (= ni (as mk-none (Maybe Bits_n))))
                              (= (select nonces (maybe-get ni)) (mk-some true))))))))

     (forall ((ctr1 Int)(ctr2 Int))
             (let ((state1 (select state ctr1))
                   (state2 (select state ctr2)))
               (=> (and (not (= none state1))
                        (not (= none state2))
                        (not (= ctr1 ctr2)))
                   (let ((u1    (el11-2 (maybe-get state1)))
                         (u2    (el11-2 (maybe-get state2)))
                         (ni1   (el11-7 (maybe-get state1)))
                         (ni2   (el11-7 (maybe-get state2)))
                         (nr1   (el11-8 (maybe-get state1)))
                         (nr2   (el11-8 (maybe-get state2))))
                     (and
                      (let ((nonce1 (ite u1 nr1 ni1))
                            (nonce2 (ite u2 nr2 ni2)))
                        (=> (not (is-mk-none nonce1))
                            (not (= nonce1 nonce2))))
                      (=> (and (not (is-mk-none ni1))
                               (not (is-mk-none nr1))
                               (= ni1 ni2)
                               (= nr1 nr2))
                          (not (= u1 u2)))))))))))




(define-fun freshness-and-honesty-matches
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (fresh (Array Int (Maybe Bool)))
     (honest (Array Int (Maybe Bool))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
    (forall ((ctr Int))
            (let ((state (select state ctr)))
              (=> (not (= state none))
                  (let ((kid (el11-4  (maybe-get state))))
                    (= (select fresh ctr)
                       (select honest kid))))))))


;; - mac key computed before use and
;; - values are actual prf evaluation
(define-fun mac-table-wellformed
    ((Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n)))
     (Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (forall ((idx (Tuple5 Int Int Int Bits_n Bits_n))
           (msg1 Bits_n) (msg2 Int))
          (let ((val-idx (mk-tuple2 idx (mk-tuple2 msg1 msg2))))
            (and (=> (is-mk-none (select Keys idx))
                     (is-mk-none (select Values val-idx)))

                 (=> (not (is-mk-none (select Values val-idx)))
                     (= (select Values val-idx)
                        (mk-some (<<func-mac>> (maybe-get (select Keys idx))
                                               msg1 msg2))))))))


(define-fun honest-sessions-to-first-and-second
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
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
                  (=> (and (> mess 1)
                           (= (select Fresh ctr) (mk-some true))
                           (or (not u)
                               (= acc (mk-some true))))
                      (ite u
                           (= (mk-some ctr) (select First (maybe-get sid)))
                           (= (mk-some ctr) (select Second (maybe-get sid))))))))))

(define-fun sessions-in-first-exist
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
          (=> (not (is-mk-none (select First sid)))
              (let ((state (select State (maybe-get (select First sid)))))
                (and (not (is-mk-none state))
                     (= (mk-some sid)
                        (el11-10 (maybe-get state))))))))


(define-fun honest-sid-have-tau-in-mac
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (and (= (select Fresh ctr)
                        (mk-some true))
                     (not (is-mk-none state)))
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
                  (=> (not (is-mk-none sid))
                      (let ((tau (el5-5 (maybe-get sid))))
                        (= (mk-some tau)
                           (select Values (mk-tuple2 (mk-tuple5 kid U V
                                                                (maybe-get ni) (maybe-get nr))
                                                     (mk-tuple2 (maybe-get nr) 2)))))))))))



(define-fun first-set-by-initiator
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Fresh (Array Int (Maybe Bool))))
  Bool
  (forall ((U Int) (V Int) (ni Bits_n) (nr Bits_n) (tau Bits_n))
          (let ((sid (mk-tuple5 U V ni nr tau)))
            (=> (not (is-mk-none (select First sid)))
                (let ((ctr (maybe-get (select First sid))))
                  (let ((kid (el11-4 (maybe-get (select State ctr))))
                        (acc  (el11-5  (maybe-get (select State ctr))))
                        (mess (el11-11 (maybe-get (select State ctr))))
                        (u   (el11-2 (maybe-get (select State ctr)))))
                    (=> (= (select Fresh ctr) (mk-some true))
                        (and (= u false)
                             (ite (= acc (mk-some true))
                                  (= mess 3)
                                  (= mess 2))))))))))

(define-fun second-set-before-initiator-accepts
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Fresh (Array Int (Maybe Bool))))
  Bool
  (forall ((U Int) (V Int) (ni Bits_n) (nr Bits_n) (tau Bits_n))
          (let ((sid (mk-tuple5 U V ni nr tau)))
            (=> (not (is-mk-none (select First sid)))
                (let ((ctr (maybe-get (select First sid))))
                  (let ((kid (el11-4 (maybe-get (select State ctr))))
                        (acc  (el11-5  (maybe-get (select State ctr))))
                        (mess (el11-11 (maybe-get (select State ctr))))
                        (u   (el11-2 (maybe-get (select State ctr)))))
                    (=> (= acc (mk-some true))
                        (not (is-mk-none (select Second sid))))))))))

(define-fun three-mac-implies-two-mac
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                         (mk-tuple2 ni 3)))))
              (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                         (mk-tuple2 nr 2))))))))

(define-fun four-mac-implies-three-mac
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
            (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                           (mk-tuple2 zeron 4)))))
                (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                           (mk-tuple2 ni 3)))))))))

(define-fun two-mac-implies-first
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                         (mk-tuple2 nr 2)))))
              (let ((tau (maybe-get (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                              (mk-tuple2 nr 2))))))
                (not (is-mk-none (select First (mk-tuple5 U V ni nr tau))))))))

(define-fun three-mac-implies-second
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                         (mk-tuple2 ni 3)))))
              (let ((tau (maybe-get (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                              (mk-tuple2 ni 3))))))
                (not (is-mk-none (select Second (mk-tuple5 U V ni nr tau))))))))



(define-fun initiator-accepts-with-mac-four-only
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall ((ctr Int))
            (let ((state (select State ctr)))
              (=> (and (not (is-mk-none state))
                       (= (mk-some true) (select Fresh ctr)))
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
                    (=> (and (= u false)
                             (= acc (mk-some true)))
                        (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                                   (mk-tuple2 zeron 4))))))))))))

(define-fun initiator-msg-2-with-mac-three-only
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (and (not (is-mk-none state))
                     (= (mk-some true) (select Fresh ctr)))
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
                  (=> (and (= u false)
                           (> mess 1))
                      (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                                 (mk-tuple2 (maybe-get ni) 3)))))))))))


(define-fun initiator-accepts-with-msg-2-only
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (and (not (is-mk-none state))
                     (= (mk-some true) (select Fresh ctr)))
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
                  (=> (and (= u false)
                           (= acc (mk-some true)))
                      (> mess 1)))))))

(define-fun responder-accepts-with-mac-three-only
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (and (not (is-mk-none state))
                     (= (mk-some true) (select Fresh ctr)))
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
                  (=> (and (= u true)
                           (= acc (mk-some true)))
                      (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                                 (mk-tuple2 (maybe-get ni) 3)))))))))))

;; if first[sid] = some ctr and state[ctr].kid is fresh
;; the state[ctr].u == false and prfvalues[...] = tau
;; (forall kid U V ni nr tau ctr

(define-fun reverse-mac-state-consistent
    ((ReverseMac (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Int)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((kid Int)(U Int)(V Int)(ni Bits_n)(nr Bits_n)(msg Bits_n)(tag Int))
          (let ((handle (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                   (mk-tuple2 msg tag))))
            (=> (not (is-mk-none (select ReverseMac handle)))
                (let ((ctr (maybe-get (select ReverseMac handle))))
                  (let ((state (select State ctr)))
                    (and (not (is-mk-none state))
                         (=> (not (is-mk-none state))
                             (let  ((Up   (el11-1  (maybe-get state)))
                                    (u    (el11-2  (maybe-get state)))
                                    (Vp   (el11-3  (maybe-get state)))
                                    (kidp (el11-4  (maybe-get state)))
                                    (acc  (el11-5  (maybe-get state)))
                                    (k    (el11-6  (maybe-get state)))
                                    (nip  (el11-7  (maybe-get state)))
                                    (nrp  (el11-8  (maybe-get state)))
                                    (kmac (el11-9  (maybe-get state)))
                                    (sid  (el11-10 (maybe-get state)))
                                    (mess (el11-11 (maybe-get state))))
                               (and (= U Up)
                                    (= V Vp)
                                    (= kid kidp)
                                    (= (mk-some ni) nip)
                                    (= (mk-some nr) nrp)))))))))))


(define-fun reverse-mac-matches
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (ReverseMac (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Int)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int)(U Int)(V Int)(ni Bits_n)(nr Bits_n)(msg Bits_n)(tag Int))
          (let ((handle (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                   (mk-tuple2 msg tag))))
            (and (= (and (is-mk-none (select ReverseMac handle))
                         (= (select H kid) (mk-some true)))
                    (is-mk-none (select Values handle)))
                 ;;(=> (not (is-mk-none (select Values handle)))
                 ;;    (= (select H kid) (mk-some true)))
                 ;;(=> (not (is-mk-none (select ReverseMac handle)))
                 ;;    (= (select H kid) (mk-some true)))
                 true))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Brainstorming on AtLeast
;;
;; For honest session U should write to one of First, Second and V should write to the other
;; To argue, we can use MAC security to notice that order of events is correct



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; For honest keys, mac values only exist when a session has passed that state
(define-fun mac-table-values
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall ((ctr Int))
            (let ((state (select State ctr)))
              (=> (and (not (is-mk-none state))
                       (= (mk-some true) (select Fresh ctr)))
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
                    (=> (and (= (select Fresh kid) (mk-some true))
                             (not (is-mk-none ni))
                             (not (is-mk-none nr)))
                        (let ((handle (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))))
                          (and (=> (not (is-mk-none (select Values (mk-tuple2 handle (mk-tuple2 zeron 4)))))
                                   (or (and (not u) (> mess 2))
                                       (and u (> mess 1)))))))))))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Use ReverseMac:
;;  - if ReverseMac has some entry then the session indicated
;;    in ReverseMac has progressed enough to have generated
;;    that message

(define-state-relation relation-mac-implies-message
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((kid Int)(U Int)(V Int)(ni Bits_n)(nr Bits_n))
     (let ((handle (mk-tuple5 kid U V ni nr)))
       (and
        (let ((ctr (select left.KX.ReverseMac (mk-tuple2 handle (mk-tuple2 zeron 4)))))
          (=> (not (is-mk-none ctr))
              (let ((state (select left.KX.State (maybe-get ctr))))
                (and (not (is-mk-none state))
                     (let ((u    (el11-2  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))
                       (and u (= acc (mk-some true)) (= mess 2)))))))

        (let ((ctr (select left.KX.ReverseMac (mk-tuple2 handle (mk-tuple2 ni 3)))))
          (=> (not (is-mk-none ctr))
              (let ((state (select left.KX.State (maybe-get ctr))))
                (and (not (is-mk-none state))
                     (let ((u    (el11-2  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))
                       (and (not u) (or (= mess 2) (= mess 3))))))))

        (let ((ctr (select left.KX.ReverseMac (mk-tuple2 handle (mk-tuple2 nr 2)))))
          (=> (not (is-mk-none ctr))
              (let ((state (select left.KX.State (maybe-get ctr))))
                (and (not (is-mk-none state))
                     (let ((u    (el11-2  (maybe-get state)))
                           (acc  (el11-5  (maybe-get state)))
                           (mess (el11-11 (maybe-get state))))
                       (and u (or (= mess 1) (= mess 2)))))))))))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Unless key corruption, if we accept the mac in Send5,
;; then it was generated in send4:
;; * Ideal mac verify looks up the entry in the table
;; * Entry is only added to the table in matching send4
;;
(define-fun message-implies-mac
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((ctr Int))
     (let ((state (select State ctr)))
       (=> (and (not (is-mk-none state))
                (= (mk-some true) (select Fresh ctr)))
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
             (and
              (=> (= mess 3)
                  (and
                   (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                              (mk-tuple2 zeron 4)))))
                   ))
              (=> (and u (or (= mess 2) (= mess 3)) (= acc (mk-some true)))
                  (and
                   (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                              (mk-tuple2 (maybe-get ni) 3)))))
                   (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                              (mk-tuple2 zeron 4)))))
                   ))
              (=> (and (not u) (or (= mess 2) (= mess 3)))
                  (and
                   (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                              (mk-tuple2 (maybe-get nr) 2)))))
                   (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                                              (mk-tuple2 (maybe-get ni) 3))))))))))))))




(define-fun three-mac-implies-first-or-second
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
            (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                           (mk-tuple2 ni 3)))))
                (let ((tau (maybe-get (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                                (mk-tuple2 ni 3))))))
                  (or (not (is-mk-none (select First (mk-tuple5 U V ni nr tau))))
                      (not (is-mk-none (select Second (mk-tuple5 U V ni nr tau))))))))))


(define-fun four-mac-implies-first-or-second
    ((Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n)))
     (First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
            (=> (not (is-mk-none (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                           (mk-tuple2 zeron 4)))))
                (let ((tau (maybe-get (select Values (mk-tuple2 (mk-tuple5 kid U V ni nr)
                                                                (mk-tuple2 ni 3))))))
                  (or (not (is-mk-none (select First (mk-tuple5 U V ni nr tau))))
                      (not (is-mk-none (select Second (mk-tuple5 U V ni nr tau))))))))))



(define-fun sessions-in-first-second-sufficiently-advanced
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((U Int) (V Int) (ni Bits_n) (nr Bits_n) (tau Bits_n))
     (let ((first (select First (mk-tuple5 U V ni nr tau))))
       (=> (not (is-mk-none first))
           (let ((state (select State (maybe-get first))))
             (and (not (is-mk-none state))
                  (let  ((mess (el11-11 (maybe-get state))))
                    (or (= mess 2)
                        (= mess 3))))))))))


(define-fun sessions-in-first-second-sufficiently-advanced-reverse
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((ctr Int))
     (let ((state (select State ctr)))
       (=> (and (not (is-mk-none state))
                (= (mk-some true) (select Fresh ctr)))
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
             (let ((first (select First (maybe-get sid))))
               (=> (not (is-mk-none first))
                   (or (= mess 2)
                       (= mess 3))))))))))

(define-fun responder-in-first-second-always-accepted
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((ctr Int))
     (let ((state (select State ctr)))
       (=> (and (not (is-mk-none state))
                (= (mk-some true) (select Fresh ctr)))
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
             (let ((first (select First (maybe-get sid)))
                   (second (select Second (maybe-get sid))))
               (and (=> (and u (= first (mk-some ctr)))
                        (= acc (mk-some true)))
                    (=> (and u (= second (mk-some ctr)))
                        (= acc (mk-some true)))))))))))

(define-fun first-second-distinct
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((U Int) (V Int) (ni Bits_n) (nr Bits_n) (tau Bits_n))
          (let ((handle (mk-tuple5 U V ni nr tau)))
            (and (=> (not (is-mk-none (select Second handle)))
                     (and (not (= (select First handle) (select Second handle)))
                          (let ((state-first (select State (maybe-get (select First handle))))
                                (state-second (select State (maybe-get (select Second handle)))))
                            (and (not (is-mk-none state-first))
                                 (not (is-mk-none state-second))
                                 (not (= (el11-2 (maybe-get state-first))
                                         (el11-2 (maybe-get state-second))))))))))))


(define-fun second-after-first
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int))))
  Bool
  (forall ((U Int) (V Int) (ni Bits_n) (nr Bits_n) (tau Bits_n))
          (let ((handle (mk-tuple5 U V ni nr tau)))
            (and (=> (is-mk-none (select First handle))
                     (is-mk-none (select Second handle)))))))


(define-fun sids-unique
    ((Fresh (Array Int (Maybe Bool)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall
   ((ctr1 Int)(ctr2 Int))
   (let ((state1 (select State ctr1))
         (state2 (select State ctr2)))
     (=> (and (not (is-mk-none state1))
              (not (is-mk-none state2))
              (= (select Fresh ctr1) (mk-some true))
              (= (select Fresh ctr2) (mk-some true)))
         (let ((u1    (el11-2 (maybe-get state1)))
               (u2    (el11-2 (maybe-get state2)))
               (sid1  (el11-10 (maybe-get state1)))
               (sid2  (el11-10 (maybe-get state2))))
           (=> (and (not (= ctr1 ctr2))
                    (not (is-mk-none sid1))
                    (= sid1 sid2))
               (not (= u1 u2)))
           )))))




;; TODO also claim for four mac
(define-fun three-mac-implies-first
    ((First (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (Second (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Int)))
     (ReverseMac (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Int)))
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (let ((zeron (<theorem-consts-Full4WHS-zeron> <<theorem-consts>>)))
    (forall
     ((kid Int)(U Int)(V Int)(ni Bits_n)(nr Bits_n))
     (and
      (let ((ctr (select ReverseMac (mk-tuple2 (mk-tuple5 kid U V ni nr) (mk-tuple2 ni 3)))))
        (=> (not (is-mk-none ctr))
            (let ((state (select State (maybe-get ctr))))
              (=> (not (is-mk-none state)) ;; should already be known
                  (let ((sid (el11-10 (maybe-get state))))
                    (=> (not (is-mk-none sid)) ;; same
                        (not (is-mk-none (select First (maybe-get sid))))))))))

      (let ((ctr (select ReverseMac (mk-tuple2 (mk-tuple5 kid U V ni nr) (mk-tuple2 zeron 4)))))
        (=> (not (is-mk-none ctr))
            (let ((state (select State (maybe-get ctr))))
              (=> (not (is-mk-none state)) ;; should already be known
                  (let ((sid (el11-10 (maybe-get state))))
                    (=> (not (is-mk-none sid)) ;; same
                        (and (not (is-mk-none (select First (maybe-get sid))))
                             (not (is-mk-none (select Second (maybe-get sid)))))))))))))))



(define-state-relation relation-trivial-equalities
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (= left.Nonces         right.Nonces)
       (= left.PRF.LTK        right.PRF.LTK)
       (= left.PRF.H          right.PRF.H)
       (= left.PRF.kid_       right.PRF.kid_)
       (= left.KX.ctr_        right.KX.ctr_)
       (= left.KX.State       right.KX.State)
       (= left.KX.RevTested   right.KX.RevTested)
       (= left.KX.RevTestEval right.KX.RevTestEval)
       (= left.KX.Fresh       right.KX.Fresh)
       (= left.MAC.Keys       right.MAC.Keys)
       (= left.MAC.Values     right.MAC.Values)
       (= left.KX.First       right.KX.First)
       (= left.KX.Second      right.KX.Second)
       (= left.KX.ReverseMac  right.KX.ReverseMac)
       (= left.PRF.PRF        right.PRF.PRF)))


(define-state-relation relation-no-overwriting
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (freshness-and-honesty-matches left.KX.State left.KX.Fresh left.PRF.H)
       (freshness-and-honesty-matches right.KX.State right.KX.Fresh right.PRF.H)

       (own-nonce-is-unique left.KX.State left.Nonces.Nonces)

       (no-overwriting-prf left.PRF.kid_ left.PRF.PRF left.PRF.H left.MAC.Keys left.MAC.Values left.PRF.LTK)
       (no-overwriting-prf right.PRF.kid_ right.PRF.PRF right.PRF.H right.MAC.Keys right.MAC.Values right.PRF.LTK)

       (no-overwriting-game left.KX.State left.KX.Fresh left.KX.ctr_)
       (no-overwriting-game right.KX.State right.KX.Fresh right.KX.ctr_)))


(define-state-relation relation-sids
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (sid-is-wellformed left.KX.State left.KX.Fresh left.MAC.Keys)
       (sid-matches left.KX.State left.KX.Fresh)
       (sids-unique left.KX.Fresh left.KX.State)))


(define-state-relation relation-wellformedness
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (kmac-and-tau-are-computed-correctly left.KX.State left.PRF.H left.PRF.LTK left.KX.Fresh left.MAC.Keys)
       (kmac-and-tau-are-computed-correctly right.KX.State right.PRF.H right.PRF.LTK right.KX.Fresh right.MAC.Keys)))


(define-state-relation relation-time
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (time-of-acceptance left.KX.State)
       (time-of-acceptance right.KX.State)

       (stuff-not-initialized-early left.KX.State left.KX.Fresh left.MAC.Keys)))


(define-state-relation relation-macs
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (mac-table-wellformed left.MAC.Keys left.MAC.Values)
       (four-mac-implies-three-mac left.MAC.Values)
       (three-mac-implies-two-mac left.MAC.Values)
       (initiator-accepts-with-mac-four-only left.MAC.Values left.KX.Fresh left.KX.State)
       (responder-accepts-with-mac-three-only left.MAC.Values left.KX.Fresh left.KX.State)
       (honest-sid-have-tau-in-mac left.KX.State left.KX.Fresh left.MAC.Values)))

(define-state-relation relation-first
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (sessions-in-first-exist left.KX.First left.KX.State)
       (sessions-in-first-exist left.KX.Second left.KX.State)

       (second-after-first left.KX.First left.KX.Second)
       (first-second-distinct left.KX.First left.KX.Second left.KX.State)
       (first-set-by-initiator left.KX.State left.KX.First left.KX.Fresh)

       (sessions-in-first-second-sufficiently-advanced left.KX.First left.KX.Fresh left.KX.State)
       (sessions-in-first-second-sufficiently-advanced left.KX.Second left.KX.Fresh left.KX.State)))

(define-state-relation relation-reverse-mac
    ((left <GameState_H7_<$<!n!>$>>)
     (right <GameState_H7_<$<!n!>$>>))
  (and (reverse-mac-matches left.MAC.Values left.KX.ReverseMac left.PRF.H)
       (reverse-mac-state-consistent left.KX.ReverseMac left.KX.State)))

(define-state-relation invariant
    ((state-H710  <GameState_H7_<$<!n!>$>>)
     (state-H711  <GameState_H7_<$<!n!>$>>))
  (and (relation-trivial-equalities  state-H710 state-H711)
       (relation-mac-implies-message state-H710 state-H711)
       (relation-no-overwriting      state-H710 state-H711)
       (relation-sids                state-H710 state-H711)
       (relation-wellformedness      state-H710 state-H711)
       (relation-time                state-H710 state-H711)
       (relation-macs                state-H710 state-H711)
       (relation-reverse-mac         state-H710 state-H711)
       (relation-first state-H710    state-H711)

       (no-ideal-values-for-dishonest-keys state-H710.PRF.H state-H710.PRF.PRF
                                           state-H710.MAC.Keys state-H710.MAC.Values)
       (message-implies-mac state-H710.MAC.Values
                            state-H710.KX.Fresh state-H710.KX.State)
       (three-mac-implies-first state-H710.KX.First state-H710.KX.Second
                                state-H710.KX.ReverseMac state-H710.KX.State)))



(define-lemma <relation-lemma-aux-H7_1_1_0-H7_1_1_1-NewKey>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_PRF_<$<!n!>$>_NewKey>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_PRF_<$<!n!>$>_NewKey>)
     (k (Maybe Bits_n)))
  (and (= H710-old.MAC H710-return.state.MAC)
       (= H711-old.MAC H711-return.state.MAC)
       (= H710-old.KX H710-return.state.KX)
       (= H711-old.KX H711-return.state.KX)))


(define-lemma <relation-lemma-aux-H7_1_1_0-H7_1_1_1-NewSession>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_NewSession>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_NewSession>)
     (U Int)(u Bool)(V Int)(kid Int))
  (and (= H710-old.MAC H710-return.state.MAC)
       (= H711-old.MAC H711-return.state.MAC)
       (= H710-old.Nonces H710-return.state.Nonces H711-old.Nonces H711-return.state.Nonces)
       (= H710-old.PRF H710-return.state.PRF)
       (= H711-old.PRF H711-return.state.PRF)
       (let ((ctr0 (return-value H710-return.value))
             (ctr1 (return-value H711-return.value)))
         (and (= ctr0 ctr1)
              (= H710-return.state.KX.First H710-old.KX.First
                 H711-return.state.KX.First H711-old.KX.First)
              (= H710-return.state.KX.Second H710-old.KX.Second
                 H711-return.state.KX.Second H711-old.KX.Second)
              (= H710-return.state.KX.ReverseMac H710-old.KX.ReverseMac
                 H711-return.state.KX.ReverseMac H711-old.KX.ReverseMac)
              (forall ((ctr Int))
                      (= (not (= ctr ctr0))
                         (= (select H710-return.state.KX.State ctr)
                            (select H710-old.KX.State ctr))
                         (= (select H711-return.state.KX.State ctr)
                            (select H711-old.KX.State ctr))
                         (= (select H710-return.state.KX.Fresh ctr)
                            (select H710-old.KX.Fresh ctr)
                            (select H711-return.state.KX.Fresh ctr)
                            (select H711-old.KX.Fresh ctr))))))))


(define-lemma  <relation-lemma-aux-H7_1_1_0-H7_1_1_1-SameKey>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_SameKey>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_SameKey>)
     (ctr1 Int)(ctr2 Int))
  (and (= H710-old.MAC H710-return.state.MAC)
       (= H711-old.MAC H711-return.state.MAC)
       (= H710-old.KX H710-return.state.KX)
       (= H711-old.KX H711-return.state.KX)
       (= H710-old.Nonces H710-return.state.Nonces H711-old.Nonces H711-return.state.Nonces)
       (= H710-old.PRF H710-return.state.PRF)
       (= H711-old.PRF H711-return.state.PRF)))


(define-lemma  <relation-lemma-aux-H7_1_1_0-H7_1_1_1-AtMost>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtMost>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtMost>)
     (ctr1 Int)(ctr2 Int)(ctr3 Int))
  (and (= H710-old.MAC H710-return.state.MAC)
       (= H711-old.MAC H711-return.state.MAC)
       (= H710-old.KX H710-return.state.KX)
       (= H711-old.KX H711-return.state.KX)
       (= H710-old.Nonces H710-return.state.Nonces H711-old.Nonces H711-return.state.Nonces)
       (= H710-old.PRF H710-return.state.PRF)
       (= H711-old.PRF H711-return.state.PRF)))


(define-lemma <relation-lemma-aux-H7_1_1_0-H7_1_1_1-AtLeast>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtLeast>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtLeast>)
     (sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
  (and (= H710-old.MAC H710-return.state.MAC)
       (= H711-old.MAC H711-return.state.MAC)
       (= H710-old.KX H710-return.state.KX)
       (= H711-old.KX H711-return.state.KX)
       (= H710-old.Nonces H710-return.state.Nonces H711-old.Nonces H711-return.state.Nonces)
       (= H710-old.PRF H710-return.state.PRF)
       (= H711-old.PRF H711-return.state.PRF)))
