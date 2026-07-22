(define-state-relation state=
    (left right)
  (forall ((ctr Int))
          (and (= (is-mk-none (select left.KX.State ctr))
                  (is-mk-none (select right.KX.State ctr)))
               (let ((state (select left.KX.State ctr)))
                 (=> (not (is-mk-none state))
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
                       (= (select right.KX.State ctr)
                          (mk-some (mk-tuple10 U u V ltk acc ni nr kmac sid mess)))))))))


(define-state-relation keys-computed-correctly
    (left right)
  (forall ((ctr Int))
          (let ((state (select left.KX.State ctr)))
            (=> (not (is-mk-none state))
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
                  (ite (or (and u (> mess 0))
                           (and (not u) (> mess 1)))
                       (= k (mk-some (<<func-prf>> ltk (mk-tuple5 U V (maybe-get ni) (maybe-get nr) true))))
                       (= k (as mk-none (Maybe Bits_n)))))))))


(define-state-relation time-of-acceptance
    (left right)
  (forall ((ctr Int))
          (let ((state (select left.KX.State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (acc  (el11-5  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (not (is-mk-none acc))
                      (ite u (> mess 1) (> mess 2))))))))


(define-state-relation time-of-nonces
    (left right)
  (forall ((ctr Int))
          (let ((state (select left.KX.State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (ni   (el11-7  (maybe-get state)))
                       (nr   (el11-8  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (and
                   ;; ni
                   (=> (> mess 0)
                       (not (is-mk-none ni)))
                   (=> (or (and (> mess 0) u)
                           (and (> mess 1) (not u)))
                       (not (is-mk-none nr)))))))))

(define-state-relation time-of-sid
    (left right)
  (forall ((ctr Int))
          (let ((state (select left.KX.State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (sid  (el11-10 (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (or (and (> mess 0) u)
                          (and (> mess 1) (not u)))
                      (not (is-mk-none sid))))))))


(define-state-relation invariant
    (left right)
  (and
   (= left.KX.kid_ right.KX.kid_)
   (= left.KX.ctr_ right.KX.ctr_)
   (= left.KX.LTK right.KX.LTK)
   (= left.KX.H right.KX.H)
   (= left.KX.Fresh right.KX.Fresh)
   (= left.KX.RevTested right.KX.RevTested)

   (state= left right)

   (keys-computed-correctly left right)

   (time-of-nonces left right)
   (time-of-sid left right)
   (time-of-acceptance left right)))
