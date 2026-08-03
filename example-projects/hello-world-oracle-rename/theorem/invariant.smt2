;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be global for **all** oracles. 
;               Having different variants for Oracle & UselessOracle would allow
;               us to prove wrong statements.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-state-relation invariant (L R)
  (= L.rand.ctr R.rand.ctr))

(define-fun <relation-trivial-medium_composition-small_composition-AnotherUsefulOracle> 
  ( (state-0  <GameState_MediumComposition_<$<!n!>$>>)
    (state-1  <GameState_SmallComposition_<$<!n!>$>>)
    (output-0 <OracleReturn_MediumComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)
    (output-1 <OracleReturn_SmallComposition_<$<!n!>$>_Rand_<$<!n!>$>_UsefulOracle>)  
  )
Bool
true
)