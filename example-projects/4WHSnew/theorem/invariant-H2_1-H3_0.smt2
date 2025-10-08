;; Main idea of this invariant proof
;; If ctr are equal in both games and they use the same randomness, then both games
;;    - produce the same output
;;    - abort iff the other aborts
;;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; Randomness mapping
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-Send1
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0      0)  ; This is the 2nd sampling in KX and samples ni.
   (= id-1      0)  ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
   ))

(define-fun randomness-mapping-Send2
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0     0)   ; This is the 3rd sampling in KX and samples nr.
   (= id-1     0)   ; This sampling happens in the Nonces package and is the 2nd sampling (in fact the last sampling, because Nonces is defined last).
   ))

(define-fun randomness-mapping-Send3
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Send4
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Send5
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Reveal
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-Test
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= id-0     2)   ; This is the 1st sampling in KX   and samples the random key in Test.
   (= id-1     2)   ; This is the 1st sampling in H1_0 and samples the random key in Test.
   ))

(define-fun randomness-mapping-NewKey
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0     1)   ; This is the 0th sampling in KX   and samples the random key in NewKey.
   (= id-1     1)   ; This is the 0th sampling in H1_0 and samples the random key in NewKey.
   ))

(define-fun randomness-mapping-NewSession
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

(define-fun randomness-mapping-SameKey
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )
(define-fun randomness-mapping-AtMost
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )
(define-fun randomness-mapping-AtLeast
	( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
	  (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
	  (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
	  (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
										; There is no randomness used in this oracle.
  false
  )

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Helper Functions
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun helper-collision-resistance-singleside ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
													(h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
													(k Bits_256))
  Bool
  (and
   (let ((entry (select h2-mac k)))                                            ; for all k
	 (=> (not (= entry (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))   ; if entry at k not none
		 (let ((kmac  (el3-1 (maybe-get entry)))
			   (nonce (el3-2 (maybe-get entry)))
			   (label (el3-3 (maybe-get entry))))
		   (= k (<<func-mac>> kmac nonce label)))))                            ; then k has been computed correctly from kmac and inputs (and is stored at correct location)
   (let ((entry (select h2-prf k)))                                            ; for all k
	 (=> (not (= entry (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))) ; if entry at k not none
		 (let ((ltk (el6-1 (maybe-get entry)))
			   (U    (el6-2 (maybe-get entry)))
			   (V    (el6-3 (maybe-get entry)))
			   (ni   (el6-4 (maybe-get entry)))
			   (nr   (el6-5 (maybe-get entry)))
			   (flag (el6-6 (maybe-get entry))))
		   (= k (<<func-prf>> ltk U V ni nr flag)))))))                        ; then k has been compute



(define-fun helper-collision-resistance-pairwise ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
												  (h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
												  (k1 Bits_256) (k2 Bits_256))
  Bool
  (and
   (let ((entry1 (select h2-prf k1))
		 (entry2 (select h2-prf k2)))
	 (=> (and (not (= entry1 (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool)))))
			  (not (= entry2 (as mk-none (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))))
		 (=> (not (= k1 k2))
			 (not (= entry1 entry2)))))
   (let ((entry1 (select h2-mac k1))
		 (entry2 (select h2-mac k2)))
	 (=> (and (not (= entry1 (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))
			  (not (= entry2 (as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int))))))
		 (=> (not (= k1 k2))
			 (not (= entry1 entry2)))))))


(define-fun helper-gamestate-singleside ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
										 (h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
										 (h2-nonces (Array Bits_256 (Maybe Bool)))
										 (U Int) (u Bool) (V Int) (ltk Bits_256)
										 (acc (Maybe Bool))
										 (k (Maybe Bits_256))
										 (ni (Maybe Bits_256))
										 (nr (Maybe Bits_256))
										 (kmac (Maybe Bits_256))
										 (sid (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))
										 (mess Int))
  Bool
  (and
   ;; (=> (not (= k (as mk-none (Maybe Bits_256))))
   ;;      (not (= kmac (as mk-none (Maybe Bits_256)))))
   (=> (not (= kmac (as mk-none (Maybe Bits_256))))
	   (and (not (= k (as mk-none (Maybe Bits_256))))
			(= kmac (mk-some (<<func-prf>> ltk (ite u V U) (ite u U V)     ; then kmac has the right value.
										   (maybe-get ni)
										   (maybe-get nr)
										   false)))
			(= (select h2-prf (maybe-get kmac))        ; then PRF value kmac is also in PRF table (at correct position).
			   (mk-some (mk-tuple6 ltk (ite u V U) (ite u U V)
								   (maybe-get ni)
								   (maybe-get nr)
								   false)))))

   (=> (not (= k (as mk-none (Maybe Bits_256))))
	   (and (not (= kmac (as mk-none (Maybe Bits_256))))
			(= k (mk-some (<<func-prf>> ltk (ite u V U) (ite u U V)        ; then k    has the right value.
										(maybe-get ni)
										(maybe-get nr)
										true)))
			(= (select h2-prf (maybe-get k))           ; then PRF value k is also in PRF table (at correct position).
			   (mk-some (mk-tuple6 ltk (ite u V U) (ite u U V)
								   (maybe-get ni)
								   (maybe-get nr)
								   true)))))
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
   (=> (not (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
	   (and
		(not (= (select h2-mac (el5-5 (maybe-get sid)))
				(as mk-none (Maybe (Tuple3 Bits_256 Bits_256 Int)))))
		(= kmac (mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid)))))))))

   (=> (< mess 1)
	   (and (= k (as mk-none (Maybe Bits_256)))
			(= kmac (as mk-none (Maybe Bits_256)))
			(= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))))
   (=> (< mess 2)
	   (= acc (as mk-none (Maybe Bool)))) ; Don't accept before message 2
   (=> (and (> mess 1) ; message large than 1
			(= acc (mk-some true))) ; accept = true
	   (and
		(not (= ni (as mk-none (Maybe Bits_256))))
		(not (= nr (as mk-none (Maybe Bits_256))))
		(not (= kmac (as mk-none (Maybe Bits_256))))
		(not (= k (as mk-none (Maybe Bits_256))))
		(= sid (mk-some (mk-tuple5 (ite u V U) (ite u U V) (maybe-get ni) (maybe-get nr)       ; then sid  has the right value.
								   (<<func-mac>> (maybe-get kmac)
												 (maybe-get nr)
												 2))))))))

(define-fun helper-gamestate-responder ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
										(h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
										(h2-nonces (Array Bits_256 (Maybe Bool)))
										(U Int) (u Bool) (V Int) (ltk Bits_256)
										(acc (Maybe Bool))
										(k (Maybe Bits_256))
										(ni (Maybe Bits_256))
										(nr (Maybe Bits_256))
										(kmac (Maybe Bits_256))
										(sid (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))
										(mess Int))
  Bool
  (=> u
	  (and
	   (=> (not (= nr (as mk-none (Maybe Bits_256))))
		   (= (select h2-nonces (maybe-get nr)) (mk-some true)))

	   (=> (> mess 0)
		   (and (not (= kmac (as mk-none (Maybe Bits_256))))
				(not (= k (as mk-none (Maybe Bits_256))))
				(not (= ni (as mk-none (Maybe Bits_256)))) ; then ni is not none.
				(not (= nr (as mk-none (Maybe Bits_256)))) ; then nr   is not none.
				(= sid (mk-some (mk-tuple5 V U (maybe-get ni) (maybe-get nr)       ; then sid  has the right value.
										   (<<func-mac>> (maybe-get kmac)
														 (maybe-get nr)
														 2)))))))))

(define-fun helper-gamestate-initiator ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
										(h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
										(h2-nonces (Array Bits_256 (Maybe Bool)))
										(U Int) (u Bool) (V Int) (ltk Bits_256)
										(acc (Maybe Bool))
										(k (Maybe Bits_256))
										(ni (Maybe Bits_256))
										(nr (Maybe Bits_256))
										(kmac (Maybe Bits_256))
										(sid (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))
										(mess Int))
  Bool
  (=> (not u)
	  (and
	   (=> (not (= ni (as mk-none (Maybe Bits_256))))
		   (= (select h2-nonces (maybe-get ni)) (mk-some true)))

	   (=> (> mess 0)
		   (not (= ni (as mk-none (Maybe Bits_256)))))
	   (=> (< mess 2)
		   (= sid (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
	   (=> (and (> mess 1))
				;(= acc (mk-some true)))
		   (and (= sid (mk-some (mk-tuple5 U V (maybe-get ni) (maybe-get nr)           ; then sid  has the right value.
										   (<<func-mac>> (maybe-get kmac)
														 (maybe-get nr)
														 2)))))))))


(define-fun helper-gamestate-pairwise ((h2-prf (Array Bits_256 (Maybe (Tuple6 Bits_256 Int Int Bits_256 Bits_256 Bool))))
									   (h2-mac (Array Bits_256 (Maybe (Tuple3 Bits_256 Bits_256 Int))))
									   (h2-nonces (Array Bits_256 (Maybe Bool)))
									   (ctr1 Int)
									   (U1 Int) (u1 Bool) (V1 Int) (ltk1 Bits_256)
									   (acc1 (Maybe Bool))
									   (key1 (Maybe Bits_256))
									   (ni1 (Maybe Bits_256))
									   (nr1 (Maybe Bits_256))
									   (kmac1 (Maybe Bits_256))
									   (sid1 (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))
									   (mess1 Int)
									   (ctr2 Int)
									   (U2 Int) (u2 Bool) (V2 Int) (ltk2 Bits_256)
									   (acc2 (Maybe Bool))
									   (key2 (Maybe Bits_256))
									   (ni2 (Maybe Bits_256))
									   (nr2 (Maybe Bits_256))
									   (kmac2 (Maybe Bits_256))
									   (sid2 (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))
									   (mess2 Int))
  Bool
  (and
   (let ((nonce1 (ite u1 nr1 ni1))
		 (nonce2 (ite u2 nr2 ni2)))
	 (=> (and (not (= ctr1 ctr2))
			  (not (= nonce1 (as mk-none (Maybe Bits_256)))))
		 (not (= nonce1 nonce2))))

   (=> (and (not (= key1 (as mk-none (Maybe Bits_256))))
			(= key1 key2))
	   (and ;(= kmac1 kmac2)
			(= ltk1 ltk2)
			;(= U1 V2) (= U2 V1)
			(= ni1 ni2 (mk-some (el6-4 (maybe-get (select h2-prf (maybe-get key1))))))
			(= nr1 nr2 (mk-some (el6-5 (maybe-get (select h2-prf (maybe-get key1))))))))

   (=> (and (not (= kmac1 (as mk-none (Maybe Bits_256))))
			(= kmac1 kmac2))
	   (and ;(= key1 key2)
			(= ltk1 ltk2)
			(= ni1 ni2 (mk-some (el6-4 (maybe-get (select h2-prf (maybe-get kmac1))))))
			(= nr1 nr2 (mk-some (el6-5 (maybe-get (select h2-prf (maybe-get kmac1))))))))

   (=> (and (not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
			(not (= sid2 (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))))))
	   (and (=> (or (= sid1 sid2)) ;(= (el5-5 (maybe-get sid1)) (el5-5 (maybe-get sid2))))
					;(= ltk1 ltk2))
				(and (= ltk1 ltk2)
					 (= kmac1 kmac2
						(mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid1))))))
						(mk-some (el3-1 (maybe-get (select h2-mac (el5-5 (maybe-get sid2)))))))))))

   (=> (and ;(not (= sid1 (as mk-none (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)))))
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
  (let ((gamestate-H2 (<game-H2-<$<!n!>$>-pkgstate-Game>     state-H2))
		(gamestate-H3 (<game-H3-<$<!n!>$>-pkgstate-Game_nochecks> state-H3))
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
		  (H2-state (<pkg-state-Game-<$<!n!>$>-State> gamestate-H2))
		  (H3-state (<pkg-state-Game_nochecks-<$<!n!>$>-State> gamestate-H3)))
	  (and
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Package states are, in general, equal
	   (= (<pkg-state-Game-<$<!n!>$>-LTK>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-LTK> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-H>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-H> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-ctr_>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-ctr_> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-kid_>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-kid_> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-RevTested>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-RevTested> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-Fresh>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-Fresh> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-First>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-First> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-Second>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-Second> gamestate-H3))
	   (= (<pkg-state-Game-<$<!n!>$>-State>          gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!n!>$>-State> gamestate-H3))
	   (= (<game-H2-<$<!n!>$>-pkgstate-Nonces> state-H2)
		  (<game-H3-<$<!n!>$>-pkgstate-Nonces> state-H3))
	   (= (<game-H2-<$<!n!>$>-pkgstate-CR> state-H2)
		  (<game-H3-<$<!n!>$>-pkgstate-CR> state-H3))
	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local Statement on MAC & PRF collision-freeness
	   (forall ((k1 Bits_256) (k2 Bits_256)) (helper-collision-resistance-pairwise   h2-prf h2-mac k1 k2))
	   (forall ((k Bits_256))                (helper-collision-resistance-singleside h2-prf h2-mac k))

	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local statement on single entries in the game state
	   (forall ((ctr Int))
			   (let ((state (select H2-state ctr)))
				 (=> (not (= state
							 (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
														 (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
														 (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
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
								  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
															  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
															  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
															  Int)))))
						  (not (= state2
								  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
															  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
															  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
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
