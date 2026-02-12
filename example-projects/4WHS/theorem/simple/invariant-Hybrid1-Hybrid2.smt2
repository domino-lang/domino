
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


(define-fun invariant
    ((left-game <GameState_Hybrid1_<$<!n!>$>>)
     (right-game <GameState_Hybrid2_<$<!n!>$>>))
  Bool
  (let ((left-game-pkg (<game-Hybrid1-<$<!n!>$>-pkgstate-KX> left-game))
        (right-prf-pkg (<game-Hybrid2-<$<!n!>$>-pkgstate-Prf> right-game))
        (right-game-pkg (<game-Hybrid2-<$<!n!>$>-pkgstate-KX> right-game)))
    (let ((left-LTK (<pkg-state-KX_NoKeys-<$<!n!>$>-LTK> left-game-pkg))
          (left-State (<pkg-state-KX_NoKeys-<$<!n!>$>-State> left-game-pkg))
          (left-Fresh (<pkg-state-KX_NoKeys-<$<!n!>$>-Fresh> left-game-pkg))
          (left-RevTested (<pkg-state-KX_NoKeys-<$<!n!>$>-RevTested> left-game-pkg))
          (left-H (<pkg-state-KX_NoKeys-<$<!n!>$>-H> left-game-pkg))
          (left-kid (<pkg-state-KX_NoKeys-<$<!n!>$>-kid_> left-game-pkg))
          (left-ctr (<pkg-state-KX_NoKeys-<$<!n!>$>-ctr_> left-game-pkg))
          ;;
          (right-LTK (<pkg-state-PRF-<$<!n!>$>-LTK> right-prf-pkg))
          (right-State (<pkg-state-KX_NoPrf-<$<!n!>$>-State> right-game-pkg))
          (right-Fresh (<pkg-state-KX_NoPrf-<$<!n!>$>-Fresh> right-game-pkg))
          (right-RevTested (<pkg-state-KX_NoPrf-<$<!n!>$>-RevTested> right-game-pkg))
          (right-H (<pkg-state-PRF-<$<!n!>$>-H> right-prf-pkg))
          (right-kid (<pkg-state-PRF-<$<!n!>$>-kid_> right-prf-pkg))
          (right-ctr (<pkg-state-KX_NoPrf-<$<!n!>$>-ctr_> right-game-pkg)))
      (and
       (= left-kid right-kid)
       (= left-ctr right-ctr)
       (= left-LTK right-LTK)
       (= left-H right-H)
       (= left-Fresh right-Fresh)
       (= left-RevTested right-RevTested)
       (state= left-State right-State right-LTK)

       (LTK-table-empty-above-max right-kid right-LTK)
       (ltk-and-h-set-together right-LTK right-H)))))
