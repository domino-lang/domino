(define-fun state=
    ((left-State (Array Int (Maybe (Tuple10 Int Bool Int Bits_256 (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (right-State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (right-Ltk (Array Int (Maybe Bits_256))))
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


(define-fun no-overwriting-prf
    ((max-kid Int)
     (Ltk (Array Int (Maybe Bits_256))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (is-mk-none (select Ltk kid)))))


(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_256)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))


(define-fun invariant
    ((left-game <GameState_KX_NoKey_<$<!n!>$>>)
     (right-game <GameState_KX_NoPrf_<$<!n!>$>>))
  Bool
  (let ((left-game-pkg (<game-KX_NoKey-<$<!n!>$>-pkgstate-Game> left-game))
        (right-prf-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Prf> right-game))
        (right-game-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Game> right-game)))
    (let ((left-LTK (<pkg-state-Game_NoKey-<$<!n!>$>-LTK> left-game-pkg))
          (left-State (<pkg-state-Game_NoKey-<$<!n!>$>-State> left-game-pkg))
          (left-Fresh (<pkg-state-Game_NoKey-<$<!n!>$>-Fresh> left-game-pkg))
          (left-RevTested (<pkg-state-Game_NoKey-<$<!n!>$>-RevTested> left-game-pkg))
          (left-H (<pkg-state-Game_NoKey-<$<!n!>$>-H> left-game-pkg))
          (left-kid (<pkg-state-Game_NoKey-<$<!n!>$>-kid_> left-game-pkg))
          (left-ctr (<pkg-state-Game_NoKey-<$<!n!>$>-ctr_> left-game-pkg))
          ;;
          (right-LTK (<pkg-state-PRF-<$<!n!>$>-LTK> right-prf-pkg))
          (right-State (<pkg-state-Game_NoPrf-<$<!n!>$>-State> right-game-pkg))
          (right-Fresh (<pkg-state-Game_NoPrf-<$<!n!>$>-Fresh> right-game-pkg))
          (right-RevTested (<pkg-state-Game_NoPrf-<$<!n!>$>-RevTested> right-game-pkg))
          (right-H (<pkg-state-PRF-<$<!n!>$>-H> right-prf-pkg))
          (right-kid (<pkg-state-PRF-<$<!n!>$>-kid_> right-prf-pkg))
          (right-ctr (<pkg-state-Game_NoPrf-<$<!n!>$>-ctr_> right-game-pkg)))
      (and
       (= left-kid right-kid)
       (= left-ctr right-ctr)
       (= left-LTK right-LTK)
       (= left-H right-H)
       (= left-Fresh right-Fresh)
       (= left-RevTested right-RevTested)
       (state= left-State right-State right-LTK)

       (no-overwriting-prf right-kid right-LTK)
       (ltk-and-h-set-together right-LTK right-H)))))
