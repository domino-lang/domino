; Main idea of this invariant proof
; If ctr are equal in both games and they use the same randomness, then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ctr afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only 1 randomness counter
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-UsefulOracle
  ( (base-ctr-0 Int) ; This is the counter in the beginning of the oracle call on the left.
    (base-ctr-1 Int) ; This is the counter in the beginning of the oracle call on the left.
    (id-0  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  Int)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (or
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      0)
    (= id-1      0))
  (and
    (= scr-1 base-ctr-1)
    (= scr-0 base-ctr-0)
    (= id-0      1)
    (= id-1      1))
  )
)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for Oracle & UselessOracle would allow to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant
  ( (state-1  <GameState_MediumComposition_<$<!n!>$>>)
    (state-0  <GameState_SmallComposition_<$<!n!>$>>))
  Bool
  (let
    ; getting ctr out of state
    ( (ctr-0 (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-SmallComposition-<$<!n!>$>-pkgstate-rand> state-0)))
      (ctr-1 (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> state-1))))

    ; ctr are equal
    (= ctr-0 ctr-1)))


(define-fun <relation-lemma-rand-is-eq-medium_composition-small_composition-UsefulOracle>
  (
    (left-old-state <GameState_MediumComposition_<$<!n!>$>>)
    (right-old-state <GameState_SmallComposition_<$<!n!>$>>)
    (return-left <OracleReturn-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle>)
    (return-right <OracleReturn-SmallComposition-<$<!n!>$>-Rand-<$<!n!>$>-UsefulOracle>)
  )
  Bool
  (and
    (rand-is-eq 0 0 (get-rand-ctr-medium_composition 0) (get-rand-ctr-small_composition 0))
    (rand-is-eq 1 1 (get-rand-ctr-medium_composition 1) (get-rand-ctr-small_composition 1))
  )
)