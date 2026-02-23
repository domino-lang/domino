; Main idea of this invariant proof
; If game states (ctr) are equal in both games and they use the same randomness, then both games 
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
    (id-0  SampleId)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (id-1  SampleId)      ; This is the sample-id, see LaTeX export for which id corresponds to which sampling.
    (scr-0 Int)      ; This is the counter which gets incremented each time a sampling is done with the same sample id.
    (scr-1 Int))     ; This is the counter which gets incremented each time a sampling is done with the same sample id.
  Bool
  (and
    (= scr-1 base-ctr-1) ; This means that the actual sampling has the same counter as the state counter initially.
    (= scr-0 base-ctr-0) ; This means that the actual sampling has the same counter as the state counter initially.
    (= id-0  (sample-id "rand" "UsefulOracle" "samplepoint"))
    (= id-1  (sample-id "rand" "UsefulOracle" "samplepoint"))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be global for **all** oracles. 
;               Having different variants for Oracle & UselessOracle would allow
;               us to prove wrong statements.
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
