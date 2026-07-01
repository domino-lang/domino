(declare-const h Int)
(declare-const d Int)
(declare-const hplusone Int)

(assert 
    (=
        (<theorem-consts-HybridSecurity-h> <<theorem-consts>>)
        h
    )
)

(assert 
    (=
        (<theorem-consts-HybridSecurity-d> <<theorem-consts>>)
        d
    )
)

(assert 
    (=
        (<theorem-consts-HybridSecurity-hplusone> <<theorem-consts>>)
        hplusone
    )
)

; hplusone = h + 1
(assert 
    (= 
        hplusone
        (+ 1 h)
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