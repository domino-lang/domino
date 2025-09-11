(define-fun =prf
    ((left-prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (right-prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (hon (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (let ((kmac-index (mk-tuple6 kid U V ni nr false))
                (k-index (mk-tuple6 kid U V ni nr true)))
            (and
             ;; (is-mk-none (select right-prf k-index))
             (=> (not (is-mk-none (select right-prf k-index)))
                 (= (select left-prf k-index)
                    (select right-prf k-index)))
             (= (select left-prf kmac-index)
                (select right-prf kmac-index))))))


(define-fun kmac-before-k
    ((Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (=> (is-mk-none (select Prf (mk-tuple6 kid U V ni nr false)))
              (is-mk-none (select Prf (mk-tuple6 kid U V ni nr true))))))

(define-fun no-overwriting-state
    ((max-ctr Int)
     (State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (=> (> ctr max-ctr)
              (is-mk-none (select State ctr)))))


(define-fun no-overwriting-prf
    ((max-kid Int)
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_256))))
  Bool
  (forall ((kid Int))
          (=> (> kid max-kid)
              (and (is-mk-none (select H kid))
                   (is-mk-none (select Ltk kid))))))

(define-fun kmac-before-sid
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
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
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (Ltk (Array Int (Maybe Bits_256))))
  Bool
  (and
   (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256) (flag Bool))
           (=> (is-mk-none (select Ltk kid))
               (is-mk-none (select Prf (mk-tuple6 kid U V ni nr flag)))))

  (forall ((ctr Int))
          (let ((state (select State ctr)))
                 (=> (not (is-mk-none state))
                  (let  ((kid  (el10-4  (maybe-get state))))
                    (not (is-mk-none (select Ltk kid)))))))))

(define-fun ltk-and-h-set-together
    ((Ltk (Array Int (Maybe Bits_256)))
     (H (Array Int (Maybe Bool))))
  Bool
  (forall ((kid Int))
          (= (is-mk-none (select Ltk kid))
             (is-mk-none (select H kid)))))

(define-fun k-prf-implies-rev-tested-sid
    ((Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
     (RevTested (Array (Tuple5 Int Int Bits_256 Bits_256 Bits_256) (Maybe Bool))))
  Bool
  (forall ((kid Int) (U Int) (V Int) (ni Bits_256) (nr Bits_256))
          (=> (not (is-mk-none (select Prf (mk-tuple6 kid U V ni nr true))))
              (let ((kmac (maybe-get (select Prf (mk-tuple6 kid U V ni nr false)))))
                (let ((tau (<<func-mac>> kmac nr 2)))
                  (not (is-mk-none (select RevTested (mk-tuple5 U V ni nr tau)))))))))


(define-fun h-and-fresh-match
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
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
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (H (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_256)))
     (Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
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
                      (= sid (mk-some (mk-tuple5 (ite u V U) (ite u U V)
                                                 (maybe-get ni) (maybe-get nr)
                                                 (<<func-mac>> (maybe-get kmac) (maybe-get nr) 2))))))))))

(define-fun kmac-requires-nonces
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
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
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
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
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((sid  (el10-9  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none sid)))))))


(define-fun no-kmac-in-send1
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
          (let ((state (select State ctr)))
            (=> (not (is-mk-none state))
                (let  ((kmac (el10-8  (maybe-get state)))
                       (mess (el10-10 (maybe-get state))))
                  (=> (= mess 0) (is-mk-none kmac)))))))


(define-fun kmac-is-wellformed
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Fresh (Array Int (Maybe Bool)))
     (Ltk (Array Int (Maybe Bits_256)))
     (Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256))))
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
                              (maybe-get (select Prf (mk-tuple6 kid
                                                                (ite u V U)
                                                                (ite u U V)
                                                                (maybe-get ni)
                                                                (maybe-get nr)
                                                                false)))
                              (<<func-prf>> (maybe-get (select Ltk kid))
                                            (ite u V U)
                                            (ite u U V)
                                            (maybe-get ni)
                                            (maybe-get nr)
                                            false)))))))))


(define-fun honest-kmac
    ((State (Array Int (Maybe (Tuple10 Int Bool Int Int (Maybe Bool)
                                       (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
                                       (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
     (Prf (Array (Tuple6 Int Int Int Bits_256 Bits_256 Bool) (Maybe Bits_256)))
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
                           (not (is-mk-none (select Prf (mk-tuple6 kid (ite u V U) (ite u U V)
                                                                   (maybe-get ni) (maybe-get nr)
                                                                   false))))))))))))


(define-fun invariant
    ((left-game <GameState_KX_NoPrf_<$<!n!>$>>)
     (right-game <GameState_KX_NoPrf_<$<!n!>$>>))
  Bool
  (let ((left-prf-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Prf> left-game))
        (left-game-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Game> left-game))
        (right-prf-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Prf> right-game))
        (right-game-pkg (<game-KX_NoPrf-<$<!n!>$>-pkgstate-Game> right-game)))
    (let ((left-LTK (<pkg-state-PRF-<$<!n!>$>-LTK> left-prf-pkg))
          (left-PRF (<pkg-state-PRF-<$<!n!>$>-PRF> left-prf-pkg))
          (left-State (<pkg-state-Game_NoPrf-<$<!n!>$>-State> left-game-pkg))
          (left-Fresh (<pkg-state-Game_NoPrf-<$<!n!>$>-Fresh> left-game-pkg))
          (left-RevTested (<pkg-state-Game_NoPrf-<$<!n!>$>-RevTested> left-game-pkg))
          (left-H (<pkg-state-PRF-<$<!n!>$>-H> left-prf-pkg))
          (left-kid (<pkg-state-PRF-<$<!n!>$>-kid_> left-prf-pkg))
          (left-ctr (<pkg-state-Game_NoPrf-<$<!n!>$>-ctr_> left-game-pkg))
          ;;
          (right-LTK (<pkg-state-PRF-<$<!n!>$>-LTK> right-prf-pkg))
          (right-PRF (<pkg-state-PRF-<$<!n!>$>-PRF> right-prf-pkg))
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
       (=prf left-PRF right-PRF left-H)
       (= left-H right-H)
       (= left-Fresh right-Fresh)
       (= left-RevTested right-RevTested)
       (= left-State right-State)

       (no-overwriting-state left-ctr left-State)
       (no-overwriting-prf left-kid left-H left-LTK)

       (kmac-requires-nonces left-State)
       (kmac-is-wellformed left-State left-Fresh left-LTK left-PRF)
       (no-kmac-in-send1 left-State)

       (sid-requires-nonces left-State)
       (sid-is-wellformed left-State left-H left-LTK left-PRF)
       (no-sid-in-send1 left-State)

       (kmac-before-sid left-State)
       (kmac-before-k left-PRF)

       (referenced-kid-exist left-State left-PRF left-LTK)

       (ltk-and-h-set-together left-LTK left-H)
       (h-and-fresh-match left-State left-Fresh left-H)
       (k-prf-implies-rev-tested-sid left-PRF left-RevTested)

       (honest-kmac left-State left-PRF left-Fresh left-H)))))
