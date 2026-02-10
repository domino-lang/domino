
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
                             (= U (ite u Vp Up))
                             (= V (ite u Up Vp))
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
     (prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (let ((none (as mk-none (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                          (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                          (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
    (forall ((ctr1 Int) (ctr2 Int))
            (let ((state1 (select state ctr1))
                  (state2 (select state ctr2)))
            (=> (and (not (= none state1))
                     (not (= none state2)))
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
                  (=> (and (not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
                           (not (= sid2 (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
                           (= (mk-tuple5 kid1 U1 V1 ni1 nr1)
                              (mk-tuple5 kid2 U2 V2 ni2 nr2)))
                      (= sid1 sid2))))))))


(define-fun sid-is-wellformed
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
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
                                       (select Keys (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr)))
                                       kmac)))
                        (and
                         (not (is-mk-none kmac))
                         (let ((tau (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2)))
                           (= (mk-tuple5 U V (maybe-get ni) (maybe-get nr) tau)
                              (maybe-get sid)))))))))))


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
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((i Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (and
           (=> (= (select H i) (as mk-none (Maybe Bool)))
               (= (select Ltk i) (as mk-none (Maybe Bits_n))))
           (=> (= (select Ltk i) (as mk-none (Maybe Bits_n)))
               (= (select H i) (as mk-none (Maybe Bool))))
           (=> (> i kid)
               (and
                (is-mk-none (select H i))
                (is-mk-none (select Ltk i))
                (is-mk-none (select Keys (mk-tuple5 i U V ni nr)))
                (is-mk-none (select Prf (mk-tuple2 i (mk-tuple5 U V ni nr true))))
                (is-mk-none (select Prf (mk-tuple2 i (mk-tuple5 U V ni nr false)))))))))


(define-fun no-overwriting-game
    ((state (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (ctr Int))
  Bool
  (forall ((i Int))
          (= (> i ctr)
             (is-mk-none (select state i)))))


(define-fun mac-keys-equal-in-prf
    ((prf0 (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (prf1 (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((in (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool))))
          (=> (= false (el5-5 (el2-2 in)))
              (= (select prf0 in)
                 (select prf1 in)))))


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
                        (not (= none state2)))
                   (let ((u1    (el11-2 (maybe-get state1)))
                         (u2    (el11-2 (maybe-get state2)))
                         (ni1   (el11-7 (maybe-get state1)))
                         (ni2   (el11-7 (maybe-get state2)))
                         (nr1   (el11-8 (maybe-get state1)))
                         (nr2   (el11-8 (maybe-get state2))))
                     (and
                      (let ((nonce1 (ite u1 nr1 ni1))
                            (nonce2 (ite u2 nr2 ni2)))
                        (=> (and (not (= ctr1 ctr2))
                                 (not (= nonce1 (as mk-none (Maybe Bits_n)))))
                            (not (= nonce1 nonce2))))))))))))


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
     (revtesteval1 (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Int)))
     (revtest (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool))))
  Bool
     (and
      (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
              (=> (not (is-mk-none (select revtesteval1 (mk-tuple5 kid U V ni nr))))
                  (= (select revtesteval1 (mk-tuple5 kid U V ni nr))
                     (select revtesteval0 (mk-tuple5 kid U V ni nr)))))))



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


(define-fun mac-table-wellformed
    ((Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n)))
     (Values (Array (Tuple2 (Tuple5 Int Int Int Bits_n Bits_n) (Tuple2 Bits_n Int)) (Maybe Bits_n))))
  Bool
  (forall ((idx (Tuple5 Int Int Int Bits_n Bits_n))
           (msg1 Bits_n)
           (msg2 Int))
          (let ((val-idx (mk-tuple2 idx (mk-tuple2 msg1 msg2))))
            (and (=> (is-mk-none (select Keys idx))
                     (is-mk-none (select Values val-idx)))

                 (=> (not (is-mk-none (select Values val-idx)))
                     (= (select Values val-idx)
                        (mk-some (<<func-mac>> (maybe-get (select Keys idx)) msg1 msg2))))))))


(define-fun no-ideal-values-for-dishonest-keys
    ((H (Array Int (Maybe Bool)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Keys (Array (Tuple5 Int Int Int Bits_n Bits_n) (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (= (select H kid) (mk-some false))
              (and
               (is-mk-none (select Keys (mk-tuple5 kid U V ni nr)))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))))



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
                


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Brainstorming on AtLeast
;;
;; For honest session U should write to one of First, Second and V should write to the other
;; To argue, we can use MAC security to notice that order of events is correct

(define-fun invariant
    ((state-H710  <GameState_H7_<$<!n!>$>>)
     (state-H711  <GameState_H7_<$<!n!>$>>))
  Bool
  (let ((nonces-H710 (<game-H7-<$<!n!>$>-pkgstate-Nonces> state-H710))
        (nonces-H711 (<game-H7-<$<!n!>$>-pkgstate-Nonces>  state-H711))
        (mac-H710 (<game-H7-<$<!n!>$>-pkgstate-MAC> state-H710))
        (mac-H711 (<game-H7-<$<!n!>$>-pkgstate-MAC>  state-H711))
        (game-H710 (<game-H7-<$<!n!>$>-pkgstate-KX> state-H710))
        (game-H711 (<game-H7-<$<!n!>$>-pkgstate-KX>  state-H711))
        (prf-H710 (<game-H7-<$<!n!>$>-pkgstate-PRF> state-H710))
        (prf-H711 (<game-H7-<$<!n!>$>-pkgstate-PRF>  state-H711)))
    (let ((ctr0 (<pkg-state-KX_noprfkey-<$<!n!>$>-ctr_> game-H710))
          (ctr1 (<pkg-state-KX_noprfkey-<$<!n!>$>-ctr_> game-H711))
          (State0 (<pkg-state-KX_noprfkey-<$<!n!>$>-State> game-H710))
          (State1 (<pkg-state-KX_noprfkey-<$<!n!>$>-State> game-H711))
          (First0 (<pkg-state-KX_noprfkey-<$<!n!>$>-First> game-H710))
          (First1 (<pkg-state-KX_noprfkey-<$<!n!>$>-First> game-H711))
          (Second0 (<pkg-state-KX_noprfkey-<$<!n!>$>-Second> game-H710))
          (Second1 (<pkg-state-KX_noprfkey-<$<!n!>$>-Second> game-H711))
          (RevTested0 (<pkg-state-KX_noprfkey-<$<!n!>$>-RevTested> game-H710))
          (RevTested1 (<pkg-state-KX_noprfkey-<$<!n!>$>-RevTested> game-H711))
          (RevTestEval0 (<pkg-state-KX_noprfkey-<$<!n!>$>-RevTestEval> game-H710))
          (RevTestEval1 (<pkg-state-KX_noprfkey-<$<!n!>$>-RevTestEval> game-H711))
          (Fresh0 (<pkg-state-KX_noprfkey-<$<!n!>$>-Fresh> game-H710))
          (Fresh1 (<pkg-state-KX_noprfkey-<$<!n!>$>-Fresh> game-H711))
          (Nonces0 (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H710))
          (Nonces1 (<pkg-state-Nonces-<$<!n!>$>-Nonces> nonces-H711))
          (Keys0 (<pkg-state-MAC-<$<!n!>$>-Keys> mac-H710))
          (Keys1 (<pkg-state-MAC-<$<!n!>$>-Keys> mac-H711))
          (Values0 (<pkg-state-MAC-<$<!n!>$>-Values> mac-H710))
          (Values1 (<pkg-state-MAC-<$<!n!>$>-Values> mac-H711))
          (kid0 (<pkg-state-PRF-<$<!n!>$>-kid_> prf-H710))
          (kid1 (<pkg-state-PRF-<$<!n!>$>-kid_> prf-H711))
          (Ltk0 (<pkg-state-PRF-<$<!n!>$>-LTK> prf-H710))
          (Ltk1 (<pkg-state-PRF-<$<!n!>$>-LTK> prf-H711))
          (Prf0 (<pkg-state-PRF-<$<!n!>$>-PRF> prf-H710))
          (Prf1 (<pkg-state-PRF-<$<!n!>$>-PRF> prf-H711))
          (H0 (<pkg-state-PRF-<$<!n!>$>-H> prf-H710))
          (H1 (<pkg-state-PRF-<$<!n!>$>-H> prf-H711)))
      (and (= nonces-H710 nonces-H711)
           (= Ltk0 Ltk1)
           (= H0 H1)
           (= kid0 kid1)
           (= ctr0 ctr1)
           (= State0 State1)
           (= RevTested0 RevTested1)
           (= Fresh0 Fresh1)
           (= Keys0 Keys1)
           (= Values0 Values1)
           (= First0 First1)
           (= Second0 Second1)
           
           (freshness-and-honesty-matches State0 Fresh0 H0)

           (revtesteval-matches-sometimes State0 RevTestEval0 RevTestEval1 RevTested0)
           
           (no-overwriting-prf kid0 Prf0 H0 Keys0 Ltk0)
           (no-overwriting-prf kid1 Prf1 H1 Keys1 Ltk1)
           
           (no-overwriting-game State0 ctr0)
           (sid-is-wellformed State0 Prf0 Fresh0 Keys0)
           (sid-is-wellformed State0 Prf1 Fresh1 Keys1)
           
           (sid-matches State0 Prf0)

           (own-nonce-is-unique State0 Nonces0)
           
           (revtesteval-populated RevTestEval0 H0 Prf0)
           (revtesteval-populated RevTestEval1 H1 Prf1)
           
           (prfeval-has-matching-session Prf0 RevTestEval0 RevTestEval1 RevTested0 State0 Fresh0 Keys0)
           
           (key-not-computed-unless-test-or-reveal State0 RevTested0 Prf0 H0 Keys0)

           (mac-keys-equal-in-prf Prf0 Prf1)
           
           (kmac-and-tau-are-computed-correctly State0 H0 Ltk0 Fresh0 Keys0)
           (kmac-and-tau-are-computed-correctly State1 H1 Ltk1 Fresh1 Keys1)
           
           (stuff-not-initialized-early State0 Fresh0 Keys0)

           (mac-table-wellformed Keys0 Values0)

           (no-ideal-values-for-dishonest-keys H0 Prf0 Keys0)

           (honest-sid-have-tau-in-mac State0 Fresh0 Values0)))))
