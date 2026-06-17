(define-state-relation state=
    ((left <GameState_Hybrid1_<$<!n!>$>>)
     (right <GameState_Hybrid2_<$<!n!>$>>))
  (and
  (forall ((ctr Int))
          (and (= (is-mk-none (select left.KX.State ctr))
                  (is-mk-none (select right.KX.State ctr)))
               (let ((state (select right.KX.State ctr)))
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
                       (let ((ltk (select right.Prf.LTK kid)))
                         (and (not (is-mk-none ltk))
                              (= (select left.KX.State ctr)
                                 (mk-some (mk-tuple10 U u V (maybe-get ltk) acc ni nr kmac sid mess))))))))))))


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
  (and
   (= left.KX.kid_ right.Prf.kid_)
   (= left.KX.ctr_ right.KX.ctr_)
   (= left.KX.LTK right.Prf.LTK)
   (= left.KX.H right.Prf.H)
   (= left.KX.Fresh right.KX.Fresh)
   (= left.KX.RevTested right.KX.RevTested)
   (state= left right)

   (LTK-table-empty-above-max right.Prf.kid_ right.Prf.LTK)
   (ltk-and-h-set-together right.Prf.LTK right.Prf.H)))
