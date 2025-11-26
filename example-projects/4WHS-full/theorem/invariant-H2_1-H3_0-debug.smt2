;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;                                                                                                      ;
;; Debugging relation on new state                                                                      ;
;;                                                                                                      ;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun <relation-debug-H2_1-H3_0-Send2>
	((H2-old <GameState_H2_<$<!n!><!b!><!true!><!zeron!>$>>)
	 (H3-old <GameState_H3_<$<!n!><!b!><!true!><!zeron!>$>>)
	 (H2-return <OracleReturn-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send2>)
	 (H3-return <OracleReturn-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send2>)
	 (ctr Int)
	 (msg Bits_256))
  Bool
  (let (
		(gamestate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game>
						(<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H2-return)))
		(gamestate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Game_nochecks>
						(<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H3-return)))
		(crstate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>
					  (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H2-return)))
		(crstate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>
					  (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H3-return)))
		(noncesstate-H2  (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>
						  (<oracle-return-H2-<$<!n!><!b!><!true!><!zeron!>$>-Game-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H2-return)))
		(noncesstate-H3  (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>
						  (<oracle-return-H3-<$<!n!><!b!><!true!><!zeron!>$>-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Send2-game-state> H3-return))))
										; We are using gamestate-H2 and gamestate-H3 here although these point to the new state!
	(let ((h2-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H2))
		  (h3-prf (<pkg-state-CR-<$<!bcr!><!n!>$>-PRFinverse> crstate-H3))
		  (h2-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H2))
		  (h3-mac (<pkg-state-CR-<$<!bcr!><!n!>$>-MACinverse> crstate-H3))
		  (h2-nonces (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> noncesstate-H2))
		  (h3-nonces (<pkg-state-Nonces-<$<!true!><!n!>$>-Nonces> noncesstate-H3))
		  (H2-state (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2))
		  (H3-state (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3)))
	  (and

	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-LTK> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-H> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-H> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-ctr_> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-kid_> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-RevTested> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Fresh> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-First> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-First> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-Second> gamestate-H3))
	   (= (<pkg-state-Game-<$<!b!><!n!><!zeron!>$>-State> gamestate-H2)
		  (<pkg-state-Game_nochecks-<$<!b!><!n!><!zeron!>$>-State> gamestate-H3))

	   (= crstate-H2 crstate-H3)

										;       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR>     state-kx)
										;          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-CR> state-kxred))

	   (= h2-nonces h3-nonces)

										;       (= (<game-H2-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces>     state-kx)
										;          (<game-H3-<$<!n!><!b!><!true!><!zeron!>$>-pkgstate-Nonces> state-kxred))

	   ;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
	   ;; Local Statement on MAC & PRF collision-freeness
	   (forall ((k1 Bits_256) (k2 Bits_256)) (helper-collision-resistance-pairwise h2-prf h2-mac k1 k2))
	   (forall ((k Bits_256)) (helper-collision-resistance-singleside h2-prf h2-mac k))

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
						   (mess2 (el11-11 (maybe-get (select H2-state ctr2)))))
					   (helper-gamestate-pairwise h2-prf h2-mac h2-nonces
												  ctr1 U1 u1 V1 ltk1 acc1 key1 ni1 nr1 kmac1 sid1 mess1
												  ctr2 U2 u2 V2 ltk2 acc2 key2 ni2 nr2 kmac2 sid2 mess2)
					   ))))))))
