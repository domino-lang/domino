;new (define-fun nonces-unique-after-message-2
;new     ((Fresh (Array Int (Maybe Bool)))
;new      (State (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
;new                                        (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
;new                                        (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int)))))
;new   Bool
;new   (forall
;new    ((ctr1 Int)(ctr2 Int))
;new    (let ((state1 (select State ctr1))
;new          (state2 (select State ctr2)))
;new      (=> (and (not (is-mk-none state1))
;new               (not (is-mk-none state2))
;new               (not (is-mk-some (select Fresh ctr1)))
;new               (not (is-mk-none (select Fresh ctr2))))
;new          (let ((U1    (el11-1 (maybe-get state1)))
;new                (U2    (el11-1 (maybe-get state2)))
;new                (u1    (el11-2 (maybe-get state1)))
;new                (u2    (el11-2 (maybe-get state2)))
;new                (V1    (el11-3 (maybe-get state1)))
;new                (V2    (el11-3 (maybe-get state2)))
;new                (ni1   (el11-7 (maybe-get state1)))
;new                (ni2   (el11-7 (maybe-get state2)))
;new                (nr1   (el11-8 (maybe-get state1)))
;new                (nr2   (el11-8 (maybe-get state2))))
;new            (=> (and (not (= ctr1 ctr2))
;new                     (= U1 U2)
;new                     (= V1 V2)
;new                     (= ni1 ni2)
;new                     (= nr1 nr2))
;new                (not (= u1 u2)))
;new            )))))

;new (define-fun no-overwriting-game
;new     ((fresh (Array Int (Maybe Bool)))
;new      (state (Array Int (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
;new                                        (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
;new                                        (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)) Int))))
;new      (ctr Int))
;new   Bool
;new   (forall ((i Int))
;new           (=> (> i ctr)
;new               (and (is-mk-none (select fresh i))
;new                    (is-mk-none (select state i))))))

(define-fun helper-collision-resistance-singleside ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
													(h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
													(k Bits_n))
  Bool
  (and
   (let ((entry (select h2-mac k)))                                            ; for all k
	 (=> (not (= entry (as mk-none (Maybe (Tuple3 Bits_n Bits_n Int)))))   ; if entry at k not none
		 (let ((kmac  (el3-1 (maybe-get entry)))
			   (nonce (el3-2 (maybe-get entry)))
			   (label (el3-3 (maybe-get entry))))
		   (= k (<<func-mac>> kmac nonce label)))))                            ; then k has been computed correctly from kmac and inputs (and is stored at correct location)
   (let ((entry (select h2-prf k)))                                            ; for all k
	 (=> (not (= entry (as mk-none (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))) ; if entry at k not none
		 (let ((ltk (el2-1 (maybe-get entry)))
               (x (el2-2 (maybe-get entry))))
           (let ((U    (el5-1 x))
			     (V    (el5-2 x))
			     (ni   (el5-3 x))
			     (nr   (el5-4 x))
			     (flag (el5-5 x)))
		   (= k (<<func-prf>> ltk (mk-tuple5 U V ni nr flag)))))))))                        ; then k has been compute



(define-fun helper-collision-resistance-pairwise ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
												  (h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
												  (k1 Bits_n) (k2 Bits_n))
  Bool
  (and
   (let ((entry1 (select h2-prf k1))
		 (entry2 (select h2-prf k2)))
	 (=> (and (not (= entry1 (as mk-none (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool))))))
			  (not (= entry2 (as mk-none (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))))
		 (=> (not (= k1 k2))
			 (not (= entry1 entry2)))))
   (let ((entry1 (select h2-mac k1))
		 (entry2 (select h2-mac k2)))
	 (=> (and (not (= entry1 (as mk-none (Maybe (Tuple3 Bits_n Bits_n Int)))))
			  (not (= entry2 (as mk-none (Maybe (Tuple3 Bits_n Bits_n Int))))))
		 (=> (not (= k1 k2))
			 (not (= entry1 entry2)))))))


(define-fun helper-gamestate-singleside ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
										 (h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
										 (h2-nonces (Array Bits_n (Maybe Bool)))
										 (U Int) (u Bool) (V Int) (ltk Bits_n)
										 (acc (Maybe Bool))
										 (k (Maybe Bits_n))
										 (ni (Maybe Bits_n))
										 (nr (Maybe Bits_n))
										 (kmac (Maybe Bits_n))
										 (sid (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))
										 (mess Int))
  Bool
  (and
   ;; (=> (not (= k (as mk-none (Maybe Bits_n))))
   ;;      (not (= kmac (as mk-none (Maybe Bits_n)))))
   (=> (not (= kmac (as mk-none (Maybe Bits_n))))
	   (and (not (= k (as mk-none (Maybe Bits_n))))
			(= kmac (mk-some (<<func-prf>> ltk (mk-tuple5 U V     ; then kmac has the right value.
										                  (maybe-get ni)
										                  (maybe-get nr)
										                  false))))
			(= (select h2-prf (maybe-get kmac))        ; then PRF value kmac is also in PRF table (at correct position).
			   (mk-some (mk-tuple2 ltk (mk-tuple5 U V
								                  (maybe-get ni)
								                  (maybe-get nr)
								                  false))))))

   (=> (not (= k (as mk-none (Maybe Bits_n))))
	   (and (not (= kmac (as mk-none (Maybe Bits_n))))
			(= k (mk-some (<<func-prf>> ltk (mk-tuple5 U V
										               (maybe-get ni)
										               (maybe-get nr)
										               true))))
			(= (select h2-prf (maybe-get k))           ; then PRF value k is also in PRF table (at correct position).
			   (mk-some (mk-tuple2 ltk (mk-tuple5 U V
								                  (maybe-get ni)
								                  (maybe-get nr)
								                  true))))))
			;; (= kmac (mk-some (<<func-prf>> ltk (ite u V U) (ite u U V)     ; then kmac has the right value.
			;;                             (maybe-get ni)
			;;                             (maybe-get nr)
			;;                             false)))
			;; (= (select h2-prf (maybe-get kmac))        ; then PRF value kmac is also in PRF table (at correct position).
			;;    (mk-some (mk-tuple6 ltk (ite u V U) (ite u U V)
			;;                     (maybe-get ni)
			;;                     (maybe-get nr)
			;;                     false)))))


   ;; sid bings kmac
   (=> (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
	   (and
		(not (= (select h2-mac (el5-5 (maybe-get sid)))
				(as mk-none (Maybe (Tuple3 Bits_n Bits_n Int)))))
		(= kmac (mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid)))))))))

   (=> (< mess 1)
	   (and (= k (as mk-none (Maybe Bits_n)))
			(= kmac (as mk-none (Maybe Bits_n)))
			(= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))))))
   (=> (< mess 2)
	   (= acc (as mk-none (Maybe Bool)))) ; Don't accept before message 2
   (=> (and (> mess 1) ; message large than 1
			(= acc (mk-some true))) ; accept = true
	   (and
		(not (= ni (as mk-none (Maybe Bits_n))))
		(not (= nr (as mk-none (Maybe Bits_n))))
		(not (= kmac (as mk-none (Maybe Bits_n))))
		(not (= k (as mk-none (Maybe Bits_n))))
		(= sid (mk-some (mk-tuple5 U V (maybe-get ni) (maybe-get nr)       ; then sid  has the right value.
								   (<<func-mac>> (maybe-get kmac)
												 (maybe-get nr)
												 2))))))))

(define-fun helper-gamestate-responder ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
										(h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
										(h2-nonces (Array Bits_n (Maybe Bool)))
										(U Int) (u Bool) (V Int) (ltk Bits_n)
										(acc (Maybe Bool))
										(k (Maybe Bits_n))
										(ni (Maybe Bits_n))
										(nr (Maybe Bits_n))
										(kmac (Maybe Bits_n))
										(sid (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))
										(mess Int))
  Bool
  (=> u
	  (and
	   (=> (not (= nr (as mk-none (Maybe Bits_n))))
		   (= (select h2-nonces (maybe-get nr)) (mk-some true)))

	   (=> (> mess 0)
		   (and (not (= kmac (as mk-none (Maybe Bits_n))))
				(not (= k (as mk-none (Maybe Bits_n))))
				(not (= ni (as mk-none (Maybe Bits_n)))) ; then ni is not none.
				(not (= nr (as mk-none (Maybe Bits_n)))) ; then nr   is not none.
				(= sid (mk-some (mk-tuple5 U V (maybe-get ni) (maybe-get nr)       ; then sid  has the right value.
										   (<<func-mac>> (maybe-get kmac)
														 (maybe-get nr)
														 2)))))))))

(define-fun helper-gamestate-initiator ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
										(h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
										(h2-nonces (Array Bits_n (Maybe Bool)))
										(U Int) (u Bool) (V Int) (ltk Bits_n)
										(acc (Maybe Bool))
										(k (Maybe Bits_n))
										(ni (Maybe Bits_n))
										(nr (Maybe Bits_n))
										(kmac (Maybe Bits_n))
										(sid (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))
										(mess Int))
  Bool
  (=> (not u)
	  (and
	   (=> (not (= ni (as mk-none (Maybe Bits_n))))
		   (= (select h2-nonces (maybe-get ni)) (mk-some true)))

	   (=> (> mess 0)
		   (not (= ni (as mk-none (Maybe Bits_n)))))
	   (=> (< mess 2)
		   (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
	   (=> (and (> mess 1))
				;(= acc (mk-some true)))
		   (and (= sid (mk-some (mk-tuple5 U V (maybe-get ni) (maybe-get nr)           ; then sid  has the right value.
										   (<<func-mac>> (maybe-get kmac)
														 (maybe-get nr)
														 2)))))))))


(define-fun helper-gamestate-pairwise ((h2-prf (Array Bits_n (Maybe (Tuple2 Bits_n (Tuple5 Int Int Bits_n Bits_n Bool)))))
									   (h2-mac (Array Bits_n (Maybe (Tuple3 Bits_n Bits_n Int))))
									   (h2-nonces (Array Bits_n (Maybe Bool)))
									   (ctr1 Int)
									   (U1 Int) (u1 Bool) (V1 Int) (ltk1 Bits_n)
									   (acc1 (Maybe Bool))
									   (key1 (Maybe Bits_n))
									   (ni1 (Maybe Bits_n))
									   (nr1 (Maybe Bits_n))
									   (kmac1 (Maybe Bits_n))
									   (sid1 (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))
									   (mess1 Int)
									   (ctr2 Int)
									   (U2 Int) (u2 Bool) (V2 Int) (ltk2 Bits_n)
									   (acc2 (Maybe Bool))
									   (key2 (Maybe Bits_n))
									   (ni2 (Maybe Bits_n))
									   (nr2 (Maybe Bits_n))
									   (kmac2 (Maybe Bits_n))
									   (sid2 (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))
									   (mess2 Int))
  Bool
  (and
   (let ((nonce1 (ite u1 nr1 ni1))
		 (nonce2 (ite u2 nr2 ni2)))
	 (=> (and (not (= ctr1 ctr2))
			  (not (= nonce1 (as mk-none (Maybe Bits_n)))))
		 (not (= nonce1 nonce2))))

   (=> (and (not (= key1 (as mk-none (Maybe Bits_n))))
			(= key1 key2))
	   (and ;(= kmac1 kmac2)
			(= ltk1 ltk2)
			;(= U1 V2) (= U2 V1)
			(= ni1 ni2 (mk-some (el5-3 (el2-2 (maybe-get (select h2-prf (maybe-get key1)))))))
			(= nr1 nr2 (mk-some (el5-4 (el2-2 (maybe-get (select h2-prf (maybe-get key1)))))))))

   (=> (and (not (= kmac1 (as mk-none (Maybe Bits_n))))
			(= kmac1 kmac2))
	   (and ;(= key1 key2)
			(= ltk1 ltk2)
			(= ni1 ni2 (mk-some (el5-3 (el2-2 (maybe-get (select h2-prf (maybe-get kmac1)))))))
			(= nr1 nr2 (mk-some (el5-4 (el2-2 (maybe-get (select h2-prf (maybe-get kmac1)))))))))

   (=> (and (not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
			(not (= sid2 (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))))))
	   (and (=> (or (= sid1 sid2)) ;(= (el5-5 (maybe-get sid1)) (el5-5 (maybe-get sid2))))
					;(= ltk1 ltk2))
				(and (= ltk1 ltk2)
					 (= kmac1 kmac2
						(mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid1))))))
						(mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid2)))))))))))

   (=> (and ;(not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n)))))
			(= (mk-some true) acc1 acc2)
			(= sid1 sid2))
	   (and (= key1 key2)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; INVARIANT STARTS HERE                        ;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant
	((state-H2 <GameState_H2_<$<!n!>$>>)
	 (state-H3 <GameState_H3_<$<!n!>$>>))
  Bool
  (let ((gamestate-H2 (<game-H2-<$<!n!>$>-pkgstate-KX>     state-H2))
		(gamestate-H3 (<game-H3-<$<!n!>$>-pkgstate-KX> state-H3))
		(crstate-H2 (<game-H2-<$<!n!>$>-pkgstate-CR>     state-H2))
		(crstate-H3 (<game-H3-<$<!n!>$>-pkgstate-CR> state-H3))
		(noncestate-H2 (<game-H2-<$<!n!>$>-pkgstate-Nonces> state-H2))
		(noncestate-H3 (<game-H3-<$<!n!>$>-pkgstate-Nonces> state-H3)))
	(let ((h2-prf (<pkg-state-CR-<$<!n!>$>-PRFinverse> crstate-H2))
		  (h3-prf (<pkg-state-CR-<$<!n!>$>-PRFinverse> crstate-H3))
		  (h2-mac (<pkg-state-CR-<$<!n!>$>-MACinverse> crstate-H2))
		  (h3-mac (<pkg-state-CR-<$<!n!>$>-MACinverse> crstate-H3))
		  (h2-nonces (<pkg-state-Nonces-<$<!n!>$>-Nonces> noncestate-H2))
		  (h3-nonces (<pkg-state-Nonces-<$<!n!>$>-Nonces> noncestate-H3))
		  (H2-state (<pkg-state-KX-<$<!n!>$>-State> gamestate-H2))
		  (H3-state (<pkg-state-KX_nochecks-<$<!n!>$>-State> gamestate-H3))
		  (H2-fresh (<pkg-state-KX-<$<!n!>$>-Fresh> gamestate-H2))
		  (H3-fresh (<pkg-state-KX_nochecks-<$<!n!>$>-Fresh> gamestate-H3))
		  (H2-ctr_ (<pkg-state-KX-<$<!n!>$>-ctr_> gamestate-H2))
		  (H3-ctr_ (<pkg-state-KX_nochecks-<$<!n!>$>-ctr_> gamestate-H3)))


	  (and
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Package states are, in general, equal
	   (= (<pkg-state-KX-<$<!n!>$>-LTK>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-LTK> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-H>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-H> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-ctr_>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-ctr_> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-kid_>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-kid_> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-RevTested>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-RevTested> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-Fresh>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-Fresh> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-First>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-First> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-Second>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-Second> gamestate-H3))
	   (= (<pkg-state-KX-<$<!n!>$>-State>          gamestate-H2)
		  (<pkg-state-KX_nochecks-<$<!n!>$>-State> gamestate-H3))
	   (= (<game-H2-<$<!n!>$>-pkgstate-Nonces> state-H2)
		  (<game-H3-<$<!n!>$>-pkgstate-Nonces> state-H3))
	   (= (<game-H2-<$<!n!>$>-pkgstate-CR> state-H2)
		  (<game-H3-<$<!n!>$>-pkgstate-CR> state-H3))
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local Statement on MAC & PRF collision-freeness
	   (forall ((k1 Bits_n) (k2 Bits_n)) (helper-collision-resistance-pairwise   h2-prf h2-mac k1 k2))
	   (forall ((k Bits_n))                (helper-collision-resistance-singleside h2-prf h2-mac k))

	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local statement on single entries in the game state
	   (forall ((ctr Int))
			   (let ((state (select H2-state ctr)))
				 (=> (not (= state
							 (as mk-none (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
														 (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
														 (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))
														 Int)))))
					 (let ((U    (el11-1  (maybe-get state)))
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
					   (and
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; For any side
						(helper-gamestate-singleside h2-prf h2-mac h2-nonces U u V ltk acc k ni nr kmac sid mess)
					;new	(nonces-unique-after-message-2 H2-fresh H2-state)
					;new	(no-overwriting-game H2-fresh H2-state H2-ctr_)
					;new    (nonces-unique-after-message-2 H3-fresh H3-state)
					;new	(no-overwriting-game H3-fresh H3-state H3-ctr_)
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; Responder
						(helper-gamestate-responder h2-prf h2-mac h2-nonces U u V ltk acc k ni nr kmac sid mess)
						;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
						;; Initiator
						(helper-gamestate-initiator h2-prf h2-mac h2-nonces U u V ltk acc k ni nr kmac sid mess)
						)))))
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Pairwise properties of game states
	   (forall ((ctr1 Int) (ctr2 Int))
			   (let ((state1 (select H2-state ctr1))
					 (state2 (select H2-state ctr2)))
				 (=> (and (not (= state1
								  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
															  (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
															  (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))
															  Int)))))
						  (not (= state2
								  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_n (Maybe Bool) (Maybe Bits_n)
															  (Maybe Bits_n) (Maybe Bits_n) (Maybe Bits_n)
															  (Maybe (Tuple5 Int Int Bits_n Bits_n Bits_n))
															  Int))))))
					 (let ((U1    (el11-1  (maybe-get (select H2-state ctr1))))
						   (U2    (el11-1  (maybe-get (select H2-state ctr2))))
						   (u1    (el11-2  (maybe-get (select H2-state ctr1))))
						   (u2    (el11-2  (maybe-get (select H2-state ctr2))))
						   (V1    (el11-3  (maybe-get (select H2-state ctr1))))
						   (V2    (el11-3  (maybe-get (select H2-state ctr2))))
						   (ltk1  (el11-4  (maybe-get (select H2-state ctr1))))
						   (ltk2  (el11-4  (maybe-get (select H2-state ctr2))))
						   (acc1  (el11-5  (maybe-get (select H2-state ctr1))))
						   (acc2  (el11-5  (maybe-get (select H2-state ctr2))))
						   (key1  (el11-6  (maybe-get (select H2-state ctr1))))
						   (key2  (el11-6  (maybe-get (select H2-state ctr2))))
						   (ni1   (el11-7  (maybe-get (select H2-state ctr1))))
						   (ni2   (el11-7  (maybe-get (select H2-state ctr2))))
						   (nr1   (el11-8  (maybe-get (select H2-state ctr1))))
						   (nr2   (el11-8  (maybe-get (select H2-state ctr2))))
						   (kmac1 (el11-9  (maybe-get (select H2-state ctr1))))
						   (kmac2 (el11-9  (maybe-get (select H2-state ctr2))))
						   (sid1  (el11-10 (maybe-get (select H2-state ctr1))))
						   (sid2  (el11-10 (maybe-get (select H2-state ctr2))))
						   (mess1 (el11-11 (maybe-get (select H2-state ctr1))))
						   (mess2 (el11-11 (maybe-get (select H2-state ctr2))))
						   )
					   (helper-gamestate-pairwise h2-prf h2-mac h2-nonces
												  ctr1 U1 u1 V1 ltk1 acc1 key1 ni1 nr1 kmac1 sid1 mess1
												  ctr2 U2 u2 V2 ltk2 acc2 key2 ni2 nr2 kmac2 sid2 mess2)
					   ))))))))
