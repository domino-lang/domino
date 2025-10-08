; Main idea of this invariant proof
; If ltk (or K) are equal (or use the same randomness), then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ltk and same table K afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only randomness for ltk
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun
  randomness-mapping-Eval
  ((ctr-mon     Int)
   (ctr-mod     Int)
   (id-mon      Int)
   (id-mod      Int)
   (icr-mon     Int)
   (icr-mod     Int))
  Bool
  (and  (= ctr-mon ctr-mod)
        (= ctr-mon icr-mod)
        (= ctr-mon icr-mod)
        (= id-mon  1)
        (= id-mod  1)))

(define-fun
  randomness-mapping-Get
  ((ctr-mon     Int)
   (ctr-mod     Int)
   (id-mon      Int)
   (id-mod      Int)
   (icr-mon     Int)
   (icr-mod     Int))
  Bool
  false)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for EVAL & GET allows to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun
  invariant-Eval
  ( (state-mod  <GameState_Modprfreal_<$<!n!>$>> )
    (state-mon  <GameState_Monprfreal_<$<!n!>$>>))
  Bool
  (let
    ( ; getting ltk, table K and rand couners out of state
      (ltk-mod (<state-modPRF-<$<!n!>$>-ltk>     (<game-Modprfreal-<$<!n!>$>-pkgstate-mod_prf> state-mod)))
      (  K-mod (<state-KeyReal-<$<!n!>$>-K>      (<game-Modprfreal-<$<!n!>$>-pkgstate-key> state-mod)))
      (ctr-mod (<game-Modprfreal-<$<!n!>$>-rand-0> state-mod))
      (ltk-mon (<state-PRFReal-<$<!n!>$>-ltk>    (<game-Monprfreal-<$<!n!>$>-pkgstate-prf> state-mon)))
      (  K-mon (<state-ReductionPRF-<$<!n!>$>-K> (<game-Monprfreal-<$<!n!>$>-pkgstate-red> state-mon)))
      (ctr-mon (<game-Monprfreal-<$<!n!>$>-rand-0> state-mon)))

    ; ltk are equal
    ; K   are equal
    ; randomness counters are equal
    (and (= ltk-mod ltk-mon)
         (= K-mod   K-mon)
         (= ctr-mon ctr-mod))))


(define-fun
  invariant-Get
  ( (state-mod  <GameState_Modprfreal_<$<!n!>$>> )
    (state-mon  <GameState_Monprfreal_<$<!n!>$>>))
  Bool
  (invariant-Eval state-mod state-mon))
