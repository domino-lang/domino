
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

