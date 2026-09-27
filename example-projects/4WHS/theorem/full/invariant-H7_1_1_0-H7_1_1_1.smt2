(define-state-relation relation-equalities
    (L R)
    (and
        (= L.PRF.LTK R.PRF.LTK)
        (= L.PRF.H R.PRF.H)
        (= L.PRF.PRF R.PRF.PRF)
        (= L.PRF.kid_ R.PRF.kid_)
        (= L.MAC.Keys R.MAC.Keys)
        (= L.MAC.Values R.MAC.Values)
        (= L.Nonces.Nonces R.Nonces.Nonces)
        (= L.KX.ctr_ R.KX.ctr_)
        (= L.KX.RevTested R.KX.RevTested)
        (= L.KX.Fresh R.KX.Fresh)
        (= L.KX.RevTestEval R.KX.RevTestEval)
        (= L.KX.First R.KX.First)
        (= L.KX.Second R.KX.Second)
        (= L.KX.State R.KX.State)))

(define-state-relation relation-first-points-to-state
    (L R)
    (forall ((sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
        (let ((first (select L.KX.First sid)))
            (=> (not (is-mk-none first))
                (let ((state (select L.KX.State (maybe-get first))))
                    (and
                        (not (is-mk-none state))
                        (= (el11-10 (maybe-get state)) (mk-some sid))))))))

(define-state-relation relation-first-entry-after-message1
    (L R)
    (forall ((sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
        (let ((first (select L.KX.First sid)))
            (=> (not (is-mk-none first))
                (let ((state (select L.KX.State (maybe-get first))))
                    (=> (not (is-mk-none state))
                        (> (el11-11 (maybe-get state)) 1)))))))

(define-state-relation relation-fresh-accepted-first-has-second
    (L R)
    (forall ((sid (Tuple5 Int Int Bits_n Bits_n Bits_n)))
        (let ((first (select L.KX.First sid)))
            (=> (not (is-mk-none first))
                (let ((state (select L.KX.State (maybe-get first))))
                    (=> (and (not (is-mk-none state))
                             (= (select L.KX.Fresh (maybe-get first)) (mk-some true))
                             (= (el11-5 (maybe-get state)) (mk-some true)))
                        (not (is-mk-none (select L.KX.Second sid)))))))))

(define-state-relation relation-keys-above-counter-empty
    (L R)
    (forall ((kid Int))
        (=> (> kid L.PRF.kid_)
            (and (is-mk-none (select L.PRF.H kid))
                 (is-mk-none (select L.PRF.LTK kid))))))

(define-state-relation relation-sessions-above-counter-empty
    (L R)
    (forall ((ctr Int))
        (=> (> ctr L.KX.ctr_)
            (and
                (is-mk-none (select L.KX.State ctr))
                (is-mk-none (select L.KX.Fresh ctr))))))

(define-state-relation relation-session-key-is-defined
    (L R)
    (forall ((ctr Int))
        (let ((state (select L.KX.State ctr)))
            (=> (not (is-mk-none state))
                (not (is-mk-none (select L.PRF.H (el11-4 (maybe-get state)))))))))

(define-state-relation relation-session-freshness-matches-honesty
    (L R)
    (forall ((ctr Int))
        (let ((state (select L.KX.State ctr)))
            (=> (not (is-mk-none state))
                (= (select L.KX.Fresh ctr)
                   (select L.PRF.H (el11-4 (maybe-get state))))))))

(define-state-relation relation-early-fresh-session-has-no-complete-transcript
    (L R)
    (forall ((ctr Int))
        (let ((state (select L.KX.State ctr)))
            (=> (and (not (is-mk-none state))
                     (= (select L.KX.Fresh ctr) (mk-some true)))
                (let ((role (el11-2 (maybe-get state)))
                      (nr (el11-8 (maybe-get state)))
                      (sid (el11-10 (maybe-get state)))
                      (mess (el11-11 (maybe-get state))))
                    (and
                        (=> (and (not role) (< mess 2))
                            (and (is-mk-none nr) (is-mk-none sid)))
                        (=> (and role (= mess 0))
                            (is-mk-none sid))))))))

(define-state-relation relation-mac3-entry-authenticates-first
    (L R)
    (forall ((kid Int)
             (U Int)
             (V Int)
             (ni Bits_n)
             (nr Bits_n))
        (let ((handle (mk-tuple5 kid U V ni nr))
              (mac2 (select L.MAC.Values
                        (mk-tuple2
                            (mk-tuple5 kid U V ni nr)
                            (mk-tuple2 nr 2))))
              (mac3 (select L.MAC.Values
                        (mk-tuple2
                            (mk-tuple5 kid U V ni nr)
                            (mk-tuple2 ni 3)))))
            (=> (not (is-mk-none mac3))
                (and
                    (not (is-mk-none mac2))
                    (not (is-mk-none
                        (select L.KX.First
                            (mk-tuple5 U V ni nr (maybe-get mac2))))))))))

(define-state-relation relation-mac4-entry-authenticates-second
    (L R)
    (let ((zero <0_n>))
        (forall ((kid Int)
                 (U Int)
                 (V Int)
                 (ni Bits_n)
                 (nr Bits_n))
            (let ((mac2 (select L.MAC.Values
                            (mk-tuple2
                                (mk-tuple5 kid U V ni nr)
                                (mk-tuple2 nr 2))))
                  (mac4 (select L.MAC.Values
                            (mk-tuple2
                                (mk-tuple5 kid U V ni nr)
                                (mk-tuple2 zero 4)))))
                (=> (not (is-mk-none mac4))
                    (and
                        (not (is-mk-none mac2))
                        (not (is-mk-none
                            (select L.KX.Second
                                (mk-tuple5 U V ni nr (maybe-get mac2)))))))))))

(define-state-relation relation-mac-values-are-correct
    (L R)
    (forall ((kid Int)
             (U Int)
             (V Int)
             (ni Bits_n)
             (nr Bits_n))
        (let ((handle (mk-tuple5 kid U V ni nr))
              (value (mk-tuple2 nr 2)))
            (=> (not (is-mk-none (select L.MAC.Values (mk-tuple2 handle value))))
                (and
                    (not (is-mk-none (select L.MAC.Keys handle)))
                    (= (select L.MAC.Values (mk-tuple2 handle value))
                       (mk-some (<<func-mac>> (maybe-get (select L.MAC.Keys handle)) nr 2))))))))

(define-state-relation relation-fresh-sid-authenticated-by-mac2
    (L R)
    (forall ((ctr Int))
        (let ((state (select L.KX.State ctr)))
            (=> (and (not (is-mk-none state))
                     (= (select L.KX.Fresh ctr) (mk-some true)))
                (let ((U (el11-1 (maybe-get state)))
                      (V (el11-3 (maybe-get state)))
                      (kid (el11-4 (maybe-get state)))
                      (ni (el11-7 (maybe-get state)))
                      (nr (el11-8 (maybe-get state)))
                      (sid (el11-10 (maybe-get state))))
                    (=> (and (not (is-mk-none ni))
                             (not (is-mk-none nr))
                             (not (is-mk-none sid)))
                        (let ((tau (el5-5 (maybe-get sid))))
                            (and
                                (= (maybe-get sid)
                                   (mk-tuple5 U V (maybe-get ni) (maybe-get nr) tau))
                                (= (select L.MAC.Values
                                     (mk-tuple2
                                        (mk-tuple5 kid U V (maybe-get ni) (maybe-get nr))
                                        (mk-tuple2 (maybe-get nr) 2)))
                                   (mk-some tau))))))))))

(define-state-relation invariant
    (L R)
    (and
        (relation-equalities L R)
        (relation-first-points-to-state L R)
        (relation-first-entry-after-message1 L R)
        (relation-fresh-accepted-first-has-second L R)
        (relation-keys-above-counter-empty L R)
        (relation-sessions-above-counter-empty L R)
        (relation-session-key-is-defined L R)
        (relation-session-freshness-matches-honesty L R)
        (relation-early-fresh-session-has-no-complete-transcript L R)
        (relation-mac3-entry-authenticates-first L R)
        (relation-mac4-entry-authenticates-second L R)
        (relation-mac-values-are-correct L R)
        (relation-fresh-sid-authenticated-by-mac2 L R)
    )
)