(define-fun state=
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (right-State (Array Int (Maybe (Tuple10 Int Bool Int Bits_256 (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (and (= (is-mk-none (select left-State ctr))
                  (is-mk-none (select right-State ctr)))
               (let ((state (select left-State ctr)))
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
                    (= (select right-State ctr)
                       (mk-some (mk-tuple10 U u V ltk acc ni nr kmac sid mess)))))))))


(define-fun keys-computed-correctly
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
                                            (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                            (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
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
                       (= k (mk-some (<<func-prf>> ltk (ite u V U) (ite u U V) (maybe-get ni) (maybe-get nr) true)))
                       (= k (as mk-none (Maybe Bits_256)))))))))


(define-fun time-of-acceptance
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
                                            (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                            (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
            (=> (not (is-mk-none state))
                (let  ((u    (el11-2  (maybe-get state)))
                       (acc  (el11-5  (maybe-get state)))
                       (mess (el11-11 (maybe-get state))))
                  (=> (not (is-mk-none acc))
                      (ite u (> mess 1) (> mess 2))))))))


(define-fun time-of-nonces
    ((left-State (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
                                            (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                            (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select left-State ctr)))
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


(define-fun invariant
    ((left-game <GameState_KX_<$<!n!>$>>)
     (right-game <GameState_KX_NoKey_<$<!n!>$>>))
  Bool
  (let ((left-game-pkg (<game-KX-<$<!n!>$>-pkgstate-Game> left-game))
        (right-game-pkg (<game-KX_NoKey-<$<!n!>$>-pkgstate-Game> right-game)))
    (let ((left-LTK (<pkg-state-Game-<$<!n!>$>-LTK> left-game-pkg))
          (left-State (<pkg-state-Game-<$<!n!>$>-State> left-game-pkg))
          (left-Fresh (<pkg-state-Game-<$<!n!>$>-Fresh> left-game-pkg))
          (left-RevTested (<pkg-state-Game-<$<!n!>$>-RevTested> left-game-pkg))
          (left-H (<pkg-state-Game-<$<!n!>$>-H> left-game-pkg))
          (left-kid (<pkg-state-Game-<$<!n!>$>-kid_> left-game-pkg))
          (left-ctr (<pkg-state-Game-<$<!n!>$>-ctr_> left-game-pkg))
          ;;
          (right-LTK (<pkg-state-Game_NoKey-<$<!n!>$>-LTK> right-game-pkg))
          (right-State (<pkg-state-Game_NoKey-<$<!n!>$>-State> right-game-pkg))
          (right-Fresh (<pkg-state-Game_NoKey-<$<!n!>$>-Fresh> right-game-pkg))
          (right-RevTested (<pkg-state-Game_NoKey-<$<!n!>$>-RevTested> right-game-pkg))
          (right-H (<pkg-state-Game_NoKey-<$<!n!>$>-H> right-game-pkg))
          (right-kid (<pkg-state-Game_NoKey-<$<!n!>$>-kid_> right-game-pkg))
          (right-ctr (<pkg-state-Game_NoKey-<$<!n!>$>-ctr_> right-game-pkg)))
      (and
       (= left-kid right-kid)
       (= left-ctr right-ctr)
       (= left-LTK right-LTK)
       (= left-H right-H)
       (= left-Fresh right-Fresh)
       (= left-RevTested right-RevTested)

       (state= left-State right-State)

       (keys-computed-correctly left-State)

       (time-of-nonces left-State)
       (time-of-acceptance left-State)))))
