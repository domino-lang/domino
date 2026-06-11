
(define-fun state=
    ((left-State (Array Int (Maybe (Tuple10 Int Bool Int Bits_n (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (right-State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
                                       (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
     (right-Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((ctr Int))
          (and (= (is-mk-none (select left-State ctr))
                  (is-mk-none (select right-State ctr)))
               (let ((state (select right-State ctr)))
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
                    (let ((ltk (select right-Ltk kid)))
                      (and (not (is-mk-none ltk))
                           (= (select left-State ctr)
                              (mk-some (mk-tuple10 U u V (maybe-get ltk) acc ni nr kmac sid mess)))))))))))


(define-fun LTK-table-empty-above-max
    ((max-kid Int)
     (Ltk (Array Int (Maybe Bits_n))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (is-mk-none (select Ltk kid)))))


(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_n)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))


(define-state-relation invariant
    ((left <GameState_Hybrid1_<$<!n!>$>>)
     (right <GameState_Hybrid2_<$<!n!>$>>))
  Bool
      (and
       (= left.KX.kid_ right.KX.kid_)
       (= left.KX.ctr_ right.KX.ctr_)
       (= left.KX.LTK right.KX.LTK)
       (= left.KX.H right.KX.H)
       (= left.KX.Fresh right.KX.Fresh)
       (= left.KX.RevTested right.KX.RevTested)
       (state= left.KX.State right.KX.State right.KX.LTK)

       (LTK-table-empty-above-max right.KX.kid_ right.KX.LTK)
       (ltk-and-h-set-together right.KX.LTK right.KX.H)))
