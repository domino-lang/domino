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
     (State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (= (or (> ctr max-ctr) (<= ctr 0))
             (is-mk-none (select State ctr)))))


(define-fun H-LTK-tables-empty-above-max
    ((max-kid Int)
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (= (or (> kid max-kid) (<= kid 0))
             (and (is-mk-none (select H kid))
                  (is-mk-none (select Ltk kid))))))


(define-fun kmac-before-sid
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el10-8  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state))))
                  (=> (is-mk-none kmac)
                      (is-mk-none sid)))))))


(define-fun referenced-kid-exist
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
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
                 (let  ((kid  (el10-4  (maybe-get state))))
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
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kid  (el10-4  (maybe-get state))))
                  (and (not (is-mk-none (select Fresh ctr)))
                       (not (is-mk-none (select H kid)))
                       (= (select Fresh ctr) (select H kid))))))))


(define-fun sid-is-wellformed
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el10-1  (maybe-get state)))
                       (u    (el10-2  (maybe-get state)))
                       (V    (el10-3  (maybe-get state)))
                       (kid  (el10-4  (maybe-get state)))
                       (acc  (el10-5  (maybe-get state)))
                       (ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (not (is-mk-none sid))
                      (= sid (mk-some (mk-tuple5 U V
                                                 (maybe-get ni) (maybe-get nr)
                                                 (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2))))))))))

(define-fun kmac-requires-nonces
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state))))
                  (=> (not (is-mk-none kmac))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun sid-requires-nonces
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state))))
                  (=> (not (is-mk-none sid))
                      (and (not (is-mk-none ni))
                           (not (is-mk-none nr)))))))))


(define-fun no-sid-in-send1
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none sid)))))))


(define-fun no-kmac-in-send1
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el10-8  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none kmac)))))))


(define-fun kmac-is-wellformed
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_n)))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el10-1  (maybe-get state)))
                       (u    (el10-2  (maybe-get state)))
                       (V    (el10-3  (maybe-get state)))
                       (kid  (el10-4  (maybe-get state)))
                       (acc  (el10-5  (maybe-get state)))
                       (ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
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
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el10-1  (maybe-get state)))
                       (u    (el10-2  (maybe-get state)))
                       (V    (el10-3  (maybe-get state)))
                       (kid  (el10-4  (maybe-get state)))
                       (acc  (el10-5  (maybe-get state)))
                       (ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
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


(define-state-relation invariant
    ((left <GameState_Hybrid2_<$<!n!>$>>)
     (right <GameState_Hybrid2_<$<!n!>$>>))
  (and
   (>= left.Prf.kid_ 0)
   (>= left.KX.ctr_ 0)
   (= left.Prf.kid_ right.Prf.kid_)
   (= left.KX.ctr_ right.KX.ctr_)
   (= left.Prf.LTK right.Prf.LTK)
   (=prf left.Prf.PRF right.Prf.PRF left.Prf.H)
   (= left.Prf.H right.Prf.H)
   (= left.KX.Fresh right.KX.Fresh)
   (= left.KX.RevTested right.KX.RevTested)
   (= left.KX.State right.KX.State)

   (no-overwriting-state left.KX.ctr_ left.KX.State)
   (H-LTK-tables-empty-above-max left.Prf.kid_ left.Prf.H left.Prf.LTK)
   (H-LTK-tables-empty-above-max right.Prf.kid_ right.Prf.H right.Prf.LTK)

   (kmac-requires-nonces left.KX.State)
   (kmac-is-wellformed left.KX.State left.KX.Fresh left.Prf.LTK left.Prf.PRF)
   (no-kmac-in-send1 left.KX.State)

   (sid-requires-nonces left.KX.State)
   (sid-is-wellformed left.KX.State left.Prf.H left.Prf.LTK left.Prf.PRF)
   (no-sid-in-send1 left.KX.State)

   (kmac-before-sid left.KX.State)
   (kmac-before-k left.Prf.PRF)
   (kmac-before-k right.Prf.PRF)

   (referenced-kid-exist left.KX.State left.Prf.PRF left.Prf.LTK)

   (ltk-and-h-set-together left.Prf.LTK left.Prf.H)
   (h-and-fresh-match left.KX.State left.KX.Fresh left.Prf.H)
   (k-prf-implies-rev-tested-sid left.Prf.PRF left.KX.RevTested)

   (honest-kmac left.KX.State left.Prf.PRF left.KX.Fresh left.Prf.H)))
