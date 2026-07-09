(define-fun max-State-and-Fresh
    ((max-ctr Int)
     (State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool))))
  Bool
  (forall ((ctr Int))
          (=>
           (> ctr max-ctr)
           (and
            (is-mk-none (select State ctr))
            (is-mk-none (select Fresh ctr))))))


(define-fun RevTested-and-PRF
    ((RevTested (Array (Tuple5 Int Int Bits_n Bits_n Bits_n) (Maybe Bool)))
     (PRF (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((U Int)
           (V Int)
           (ni Bits_n)
           (nr Bits_n)
           (kid Int))
          (let ((kmac-index (mk-tuple2 kid (mk-tuple5 U V ni nr false)))
                (k-index    (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
            (=>
             (not (is-mk-none (select PRF kmac-index)))
             (let ((kmac (maybe-get (select PRF kmac-index))))
               (let ((tau (<<func-mac>> kmac nr 2)))
                 (=>
                  (is-mk-none (select RevTested (mk-tuple5 U V ni nr tau)))
                  (is-mk-none (select PRF k-index)))))))))


(define-fun if-kmac-none-then-prf-none
    ((PRF (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((U Int)
           (V Int)
           (ni Bits_n)
           (nr Bits_n)
           (kid Int))
          (=>
           (is-mk-none (select PRF (mk-tuple2 kid (mk-tuple5 U V ni nr false))))
           (is-mk-none (select PRF (mk-tuple2 kid (mk-tuple5 U V ni nr true)))))))


(define-fun State-properties
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (H (Array Int (Maybe Bool)))
     (PRF (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((U    (el10-1  (maybe-get state)))
                       (role (el10-2  (maybe-get state)))
                       (V    (el10-3  (maybe-get state)))
                       (kid  (el10-4  (maybe-get state)))
                       (acc  (el10-5  (maybe-get state)))
                       (ni   (el10-6  (maybe-get state)))
                       (nr   (el10-7  (maybe-get state)))
                       (kmac (el10-8  (maybe-get state)))
                       (sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (and
                   (=>
                    (not (is-mk-none acc))
                    (or
                     (and (>= mess 3) (not role))
                     (and (>= mess 2) role)))
                   (=>
                    (and (>= mess 1) role)
                    (and
                     (not (is-mk-none ni))
                     (not (is-mk-none nr))
                     (=>
                      (= (select H kid) (mk-some true))
                      (and
                       (= sid
                          (mk-some (mk-tuple5 U V
                                               (maybe-get ni)
                                               (maybe-get nr)
                                               (<<func-mac>> (maybe-get kmac)
                                                             (maybe-get nr)
                                                             2))))
                       (= kmac
                          (select PRF (mk-tuple2 kid
                                                 (mk-tuple5 U V
                                                            (maybe-get ni)
                                                            (maybe-get nr)
                                                            false))))
                       (not (is-mk-none kmac))))))
                   (=>
                    (and (>= mess 2) (not role))
                    (and
                     (not (is-mk-none nr))
                     (=>
                      (= (select H kid) (mk-some true))
                      (and
                       (= sid
                          (mk-some (mk-tuple5 U V
                                               (maybe-get ni)
                                               (maybe-get nr)
                                               (<<func-mac>> (maybe-get kmac)
                                                             (maybe-get nr)
                                                             2))))
                       (= kmac
                          (select PRF (mk-tuple2 kid
                                                 (mk-tuple5 U V
                                                            (maybe-get ni)
                                                            (maybe-get nr)
                                                            false))))
                       (not (is-mk-none kmac))))))
                   (=>
                    (and (>= mess 1) (not role))
                    (not (is-mk-none ni)))))))))


(define-fun Fresh-State-H-LTK
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (H (Array Int (Maybe Bool)))
     (LTK (Array Int (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (and
             (=>
              (= (select Fresh ctr) (mk-some true))
              (and
               (not (is-mk-none state))
               (let ((kid (el10-4 (maybe-get state))))
                 (= (select H kid) (mk-some true)))))
             (=>
              (not (is-mk-none state))
              (let ((kid (el10-4 (maybe-get state))))
                (not (is-mk-none (select LTK kid)))))))))


(define-fun max-key
    ((max-kid Int)
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (=>
           (not (is-mk-none (select H kid)))
           (<= kid max-kid))))


(define-fun LTK-and-H-set-together
    ((H (Array Int (Maybe Bool)))
     (LTK (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select H kid))
             (is-mk-none (select LTK kid)))))


(define-fun =prf
    ((left-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n)))
     (right-prf (Array (Tuple2 Int (Tuple5 Int Int Bits_n Bits_n Bool)) (Maybe Bits_n))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_n) (nr Bits_n))
          (let ((kmac-index (mk-tuple2 kid (mk-tuple5 U V ni nr false)))
                (k-index    (mk-tuple2 kid (mk-tuple5 U V ni nr true))))
            (and
             (= (select left-prf kmac-index)
                (select right-prf kmac-index))
             (=>
              (is-mk-none (select left-prf k-index))
              (is-mk-none (select right-prf k-index)))))))


(define-state-relation invariant
    ((left <GameState_Hybrid2_<$<!n!>$>>)
     (right <GameState_Hybrid2_<$<!n!>$>>))
  (and
   (= left.Prf.kid_ right.Prf.kid_)
   (= left.KX.ctr_ right.KX.ctr_)
   (= left.Prf.H right.Prf.H)
   (= left.KX.State right.KX.State)
   (= left.Prf.LTK right.Prf.LTK)
   (= left.KX.RevTested right.KX.RevTested)
   (= left.KX.Fresh right.KX.Fresh)
   (=prf left.Prf.PRF right.Prf.PRF)

   (Fresh-State-H-LTK left.KX.State left.KX.Fresh left.Prf.H left.Prf.LTK)
   (RevTested-and-PRF left.KX.RevTested left.Prf.PRF)
   (State-properties left.KX.State left.Prf.H left.Prf.PRF)
   (if-kmac-none-then-prf-none left.Prf.PRF)
   (max-State-and-Fresh left.KX.ctr_ left.KX.State left.KX.Fresh)
   (max-key left.Prf.kid_ left.Prf.H)
   (LTK-and-H-set-together left.Prf.H left.Prf.LTK)))