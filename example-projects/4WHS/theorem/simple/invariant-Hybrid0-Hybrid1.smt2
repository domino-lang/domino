(define-state-relation state=
    ((left <GameState_Hybrid0_<$<!n!>$>>)
     (right <GameState_Hybrid1_<$<!n!>$>>))
  (forall ((ctr Int))
          (and (= (is-mk-none (select left.KX.State ctr))
                  (is-mk-none (select right.KX.State ctr)))
               (let ((state (select left.KX.State ctr)))
                 (=> (not (is-mk-none state))
                     (let  ((U    (el11-1  (maybe-get state)))
                            (role (el11-2  (maybe-get state)))
                            (V    (el11-3  (maybe-get state)))
                            (ltk  (el11-4  (maybe-get state)))
                            (acc  (el11-5  (maybe-get state)))
                            (k    (el11-6  (maybe-get state)))
                            (ni   (el11-7  (maybe-get state)))
                            (nr   (el11-8  (maybe-get state)))
                            (kmac (el11-9  (maybe-get state)))
                            (sid  (el11-10 (maybe-get state)))
                            (mess (el11-11 (maybe-get state))))
                       (and
                        (= (select right.KX.State ctr)
                           (mk-some (mk-tuple10 U role V ltk acc ni nr kmac sid mess)))
                        (=>
                         (or
                          (and role (> mess 0))
                          (and (not role) (> mess 1)))
                         (= k (mk-some (<<func-prf>> ltk
                                                       (mk-tuple5 U V
                                                                  (maybe-get ni)
                                                                  (maybe-get nr)
                                                                  true)))))
                        (=>
                         (not (is-mk-none acc))
                         (or
                          (and role (> mess 1))
                          (and (not role) (> mess 2))))
                        (=>
                         (and (not role) (> mess 0))
                         (not (is-mk-none ni)))
                        (=>
                         (and (not role) (> mess 1))
                         (not (is-mk-none nr)))
                        (=>
                         (and role (> mess 0))
                         (and
                          (not (is-mk-none ni))
                          (not (is-mk-none nr))))
                        (=> ; needed for sid Unwraps in Send3 and Send4
                         (or
                          (and role (> mess 0))
                          (and (not role) (> mess 1)))
                         (not (is-mk-none sid))))))))))


(define-state-relation invariant
    ((left <GameState_Hybrid0_<$<!n!>$>>)
     (right <GameState_Hybrid1_<$<!n!>$>>))
  (and
   (= left.KX.kid_ right.KX.kid_)
   (= left.KX.ctr_ right.KX.ctr_)
   (= left.KX.LTK right.KX.LTK)
   (= left.KX.H right.KX.H)
   (= left.KX.Fresh right.KX.Fresh)
   (= left.KX.RevTested right.KX.RevTested)

   (state= left right)))
