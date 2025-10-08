; Main idea of this invariant proof
; If ltk (or K) are equal (or use the same randomness), then both games 
;    - produce the same output
;    - abort iff the other aborts
;    - have same ltk and same K afterwards

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Randomness mapping --- there is only randomness for ltk
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun randomness-mapping-Eval (
        (ltk-mod     Bits_n)
        (ltk-mon     Bits_n))
        Bool
        true
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant --- note that the invariant needs to be game-global 
;               Having different variants for Eval & Get allows to prove wrong things.
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-Eval      (
        (state-mod  CompositionState-modprfreal )
        (state-mon  CompositionState-monprfreal)
)
    Bool
    (let

; getting ltk and table K out
(
(ltk-mod (state-modprfreal-modprf-ltk     (composition-pkgstate-modprfreal-modprf state-mod)))
(  K-mod (state-modprfreal-key-K          (composition-pkgstate-modprfreal-modprf state-mod)))
(ltk-mon (state-monprfreal-monprfreal-ltk (composition-pkgstate-modprfreal-modprf state-mon)))
(  K-mon (state-monprfreal-red-K          (composition-pkgstate-modprfreal-modprf state-mon)))


(and
; ltk are equal
; T   are equal
(= ltk-mod ltk-mon)
(= K-mod   K-mon)
)

)))
