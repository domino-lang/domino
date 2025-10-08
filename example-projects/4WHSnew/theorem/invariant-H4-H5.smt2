; Main idea of this invariant proof
; If ctr are equal in both games and they use the same randomness, then both games
;    - produce the same output
;    - abort iff the other aborts
;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping
;
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


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
										;                                                                                                      ;
										; Invariant --- note that the invariant needs to be game-global and not per oracle,                    ;
										;               so that induction over the oracle calls remains meaningful.                            ;
										;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun state-equality
	((state-H4 (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
										  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
										  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int))))
	 (state-H5 (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
										  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
										  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
		  (and (=> (= (select state-H5 ctr)
					  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
												  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
												  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
												  Int))))
				   (= (select state-H4 ctr) (select state-H5 ctr)))
			   (=> (= (select state-H4 ctr)
					  (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
												  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
												  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
												  Int))))
				   (= (select state-H4 ctr) (select state-H5 ctr)))
			   (let ((state (select state-H4 ctr)))
				 (=> (not (= state
							 (as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
														 (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
														 (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
														 Int)))))

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
					   (= (select state-H5 ctr)
						  (mk-some (mk-tuple11 U u V ltk acc (as mk-none (Maybe Bits_256))
											   ni nr kmac sid mess)))))))))


(define-fun invariant-H4
	((state-H4 (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
										  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
										  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
		  (let ((state (select state-H4 ctr)))
			(=> (not (= state
						(as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
													(Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
													(Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
													Int)))))
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
				  (and
				   (=> (> 1 mess)
					   (= k (as mk-none (Maybe Bits_256))))
				   (=> u (=> (> mess 0)
							 (and (not (= ni (as mk-none (Maybe Bits_256))))
								  (not (= nr (as mk-none (Maybe Bits_256))))
								  (not (= k (as mk-none (Maybe Bits_256)))))))
				   (=> (> mess 1)
					   (and (not (= ni (as mk-none (Maybe Bits_256))))
							(not (= nr (as mk-none (Maybe Bits_256))))
							(not (= k (as mk-none (Maybe Bits_256))))))
				   (=> (= acc (mk-some true))
					   (not (= k (as mk-none (Maybe Bits_256)))))
				   (=> (not (= k (as mk-none (Maybe Bits_256))))
					   (and (= k (mk-some (<<func-prf>> ltk (ite u V U) (ite u U V)
														(maybe-get ni)
														(maybe-get nr)
														true)))))))))))

(define-fun invariant-H5
	((state-H5 (Array Int (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
										  (Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
										  (Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256)) Int)))))
  Bool
  (forall ((ctr Int))
		  (let ((state (select state-H5 ctr)))
			(=> (not (= state
						(as mk-none (Maybe (Tuple11 Int Bool Int Bits_256 (Maybe Bool) (Maybe Bits_256)
													(Maybe Bits_256) (Maybe Bits_256) (Maybe Bits_256)
													(Maybe (Tuple5 Int Int Bits_256 Bits_256 Bits_256))
													Int)))))
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
				  (and
				   (=> (= acc (mk-some true))
					   (and (not (= ni (as mk-none (Maybe Bits_256))))
							(not (= nr (as mk-none (Maybe Bits_256))))))))))))

(define-fun invariant
	((state-H4  <GameState_H4_<$<!n!>$>>)
	 (state-H5  <GameState_H5_<$<!n!>$>>))
  Bool
  (let ((gamestate-H4 (<game-H4-<$<!n!>$>-pkgstate-Game_nochecks> state-H4))
		(gamestate-H5 (<game-H5-<$<!n!>$>-pkgstate-Game_nokey> state-H5))
		(noncestate-H4 (<game-H4-<$<!n!>$>-pkgstate-Nonces> state-H4))
		(noncestate-H5 (<game-H5-<$<!n!>$>-pkgstate-Nonces> state-H5)))
	(and (= (<pkg-state-Nonces-<$<!n!>$>-Nonces> noncestate-H4)
			(<pkg-state-Nonces-<$<!n!>$>-Nonces> noncestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-LTK> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-LTK>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-ctr_> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-ctr_>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-H> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-H>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-kid_> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-kid_>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-RevTested> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-RevTested>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-Fresh> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-Fresh>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-First> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-First>    gamestate-H5))
		 (= (<pkg-state-Game_nochecks-<$<!n!>$>-Second> gamestate-H4)
			(<pkg-state-Game_nokey-<$<!n!>$>-Second>    gamestate-H5))

		 (let ((state-H4 (<pkg-state-Game_nochecks-<$<!n!>$>-State> gamestate-H4))
			   (state-H5 (<pkg-state-Game_nokey-<$<!n!>$>-State>    gamestate-H5)))
		   (and (state-equality state-H4 state-H5)
				(invariant-H4 state-H4)
				(invariant-H5 state-H5))))))
