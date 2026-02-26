(define-fun =prf
    ((left-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (right-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (hon (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (let ((kmac-index (mk-tuple2 kid (mk-tuple5 U V ni nr false)))
                (k-index (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
            (and
             ;; (is-mk-none (select right-prf k-index))
             (=> (not (is-mk-none (select right-prf k-index)))
                 (= (select left-prf k-index)
                    (select right-prf k-index)))
             (= (select left-prf kmac-index)
                (select right-prf kmac-index))))))


(define-fun no-overwriting-state
    ((max-ctr Int)
     (State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (=> (> ctr max-ctr)
              (is-mk-none (select State ctr)))))


(define-fun H-LTK-tables-empty-above-max
    ((max-kid Int)
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (and (is-mk-none (select H kid))
                   (is-mk-none (select Ltk kid))))))


(define-fun kmac-before-sid
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el11-9  (maybe-get state)))
                       (sid  (el11-10  (maybe-get state))))
                  (=> (is-mk-none kmac)
                      (is-mk-none sid)))))))


(define-fun referenced-kid-exist
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))

     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (and
   (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n) (flag Bool))
           (=> (is-mk-none (select Ltk kid))
               (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr flag))))))

   (forall ((ctr Int))
           (let ((state (select State ctr)))
             (=> (not (is-mk-none state))
                 (let  ((kid  (el11-4  (maybe-get state))))
                   (not (is-mk-none (select Ltk kid)))))))))


(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_n)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))


(define-fun k-prf-implies-rev-tested-sid
    ((Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (RevTested (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (not (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))
              (let ((kmac (maybe-get (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))))
                (let ((tau (<<func-mac>> kmac nr 2)))
                  (not (is-mk-none (select RevTested (mk-tuple5 U V ni nr tau)))))))))


(define-fun h-and-fresh-match
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))

     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kid  (el11-4  (maybe-get state))))
                  (and (not (is-mk-none (select Fresh ctr)))
                       (not (is-mk-none (select H kid)))
                       (= (select Fresh ctr) (select H kid))))))))


(define-fun sid-is-wellformed
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))

     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el11-1  (maybe-get state)))
                       (u    (el11-2  (maybe-get state)))
                       (V    (el11-3  (maybe-get state)))
                       (kid  (el11-4  (maybe-get state)))
                       (acc  (el11-6  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (kmac (el11-9  (maybe-get state)))
                       (sid  (el11-10  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (not (is-mk-none sid))
                      (= sid (mk-some (mk-tuple5 U V
                                                 (maybe-get ni) (maybe-get nr)
                                                 (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2))))))))))

(define-fun kmac-requires-nonces
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el11-8  (maybe-get state)))
                       (nr   (el11-9  (maybe-get state)))
                       (kmac (el11-10  (maybe-get state))))
                  (=> (not (is-mk-none kmac))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun sid-requires-nonces
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (sid  (el11-10  (maybe-get state))))
                  (=> (not (is-mk-none sid))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun no-sid-in-send1
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((sid  (el11-10  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none sid)))))))


(define-fun no-kmac-in-send1
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el11-9  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none kmac)))))))


(define-fun kmac-is-wellformed
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))

     (Fresh (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el11-1  (maybe-get state)))
                       (u    (el11-2  (maybe-get state)))
                       (V    (el11-3  (maybe-get state)))
                       (kid  (el11-4  (maybe-get state)))
                       (acc  (el11-6  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (kmac (el11-9  (maybe-get state)))
                       (sid  (el11-10  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (not (is-mk-none kmac))
                      (= (maybe-get kmac)
                         (ite (= (select Fresh ctr) (mk-some true))
                              (maybe-get (select Prf (mk-tuple2 kid (mk-tuple5
                                                                     U V
                                                                     (maybe-get ni)
                                                                     (maybe-get nr)
                                                                     false))))
                              (<<func-prf>> (maybe-get (select Ltk kid))
                                            (mk-tuple5 U V
                                                       (maybe-get ni)
                                                       (maybe-get nr)
                                                       false))))))))))


(define-fun honest-kmac
    ((State (Array Int (Maybe (Tuple11 Int Bool Int Int (Maybe Bool) (Maybe Bits_n)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el11-1  (maybe-get state)))
                       (u    (el11-2  (maybe-get state)))
                       (V    (el11-3  (maybe-get state)))
                       (kid  (el11-4  (maybe-get state)))
                       (acc  (el11-6  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (kmac (el11-9  (maybe-get state)))
                       (sid  (el11-10  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (= (select Fresh ctr)
                         (mk-some true))
                      (and
                       (= (select H kid) (mk-some true))
                       (=> (not (is-mk-none kmac))
                           (not (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V
                                                                                  (maybe-get ni) (maybe-get nr)

                                                                                  false)))))))))))))


(define-fun kmac-before-k
    ((Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool))
                 (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (=> (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
              (is-mk-none (select Prf (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))))


(define-state-relation relation-trivial-equalities
    ((left <GameState_H6_<$<!n!>$>>)
     (right <GameState_H6_<$<!n!>$>>))
  (and (= left.Nonces       right.Nonces)
       (= left.PRF.kid_     right.PRF.kid_)
       (= left.KX.ctr_      right.KX.ctr_)
       (= left.PRF.LTK      right.PRF.LTK)
       (= left.PRF.H        right.PRF.H)
       (= left.KX.Fresh     right.KX.Fresh)
       (= left.KX.RevTested right.KX.RevTested)
       (= left.KX.First     right.KX.First)
       (= left.KX.Second    right.KX.Second)
       (= left.KX.State     right.KX.State)))

(define-state-relation invariant
    ((left <GameState_H6_<$<!n!>$>>)
     (right <GameState_H6_<$<!n!>$>>))
  (and (relation-trivial-equalities left right)
       (=prf left.PRF.PRF right.PRF.PRF left.PRF.H)

       (no-overwriting-state left.KX.ctr_ left.KX.State)
       (H-LTK-tables-empty-above-max left.PRF.kid_  left.PRF.H  left.PRF.LTK)
       (H-LTK-tables-empty-above-max right.PRF.kid_ right.PRF.H right.PRF.LTK)

       (kmac-requires-nonces left.KX.State)
       (kmac-is-wellformed left.KX.State left.KX.Fresh left.PRF.LTK left.PRF.PRF)
       (no-kmac-in-send1 left.KX.State)

       (sid-requires-nonces left.KX.State)
       (sid-is-wellformed left.KX.State left.PRF.H left.PRF.LTK left.PRF.PRF)
       (no-sid-in-send1 left.KX.State)

       (kmac-before-sid left.KX.State)
       (kmac-before-k left.PRF.PRF)
       (kmac-before-k right.PRF.PRF)

       (referenced-kid-exist left.KX.State left.PRF.PRF left.PRF.LTK)

       (ltk-and-h-set-together left.PRF.LTK left.PRF.H)
       (h-and-fresh-match left.KX.State left.KX.Fresh left.PRF.H)
       (k-prf-implies-rev-tested-sid left.PRF.PRF left.KX.RevTested)

       (honest-kmac left.KX.State left.PRF.PRF left.KX.Fresh left.PRF.H)))


(define-lemma <relation-aux-H6_1_0-H6_1_1-AtLeast>
    ((H610-old <GameState_H6_<$<!n!>$>>)
     (H611-old <GameState_H6_<$<!n!>$>>)
     (H610-return <OracleReturn_H6_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtLeast>)
     (H611-return <OracleReturn_H6_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_AtLeast>)
     (sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
  (and (= H610-return.state.KX H610-old.KX)
       (= H611-return.state.KX H611-old.KX)
       (= H610-return.state.Nonces H610-old.Nonces
          H611-return.state.Nonces H611-old.Nonces)
       (= H610-return.state.PRF H610-old.PRF)
       (= H611-return.state.PRF H611-old.PRF)))
