;; (declare-const h Int)
;; (declare-const d Int)

;; (assert 
;;     (=
;;         (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>)
;;         h
;;     )
;; )

;; (assert 
;;     (=
;;         (<theorem-consts-HybridSecurity-d> <<theorem-consts>>)
;;         d
;;     )
;; )

; h > 0 for SETBIT and GETAOUT
(assert
    (< 0 (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>) (<theorem-consts-HybridSecurity-d> <<theorem-consts>>))
)

;; ; h < d for GETKEYSIN
;; (assert
;;     (< h d)
;; )
