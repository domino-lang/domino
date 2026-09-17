(declare-const h Int)
(declare-const d Int)

(assert 
    (=
        (<theorem-consts-HybridSecurity-hybrid$loop> <<theorem-consts>>)
        h
    )
)

(assert 
    (=
        (<theorem-consts-HybridSecurity-d> <<theorem-consts>>)
        d
    )
)

; h > 0 for SETBIT and GETAOUT
(assert
    (> h 0)
)

; h < d for GETKEYSIN
(assert
    (< h d)
)
