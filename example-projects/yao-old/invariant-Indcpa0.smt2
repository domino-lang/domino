
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T    (Maybe (Array Bool (Maybe Bits_n))))
      (state-keys-z    (Maybe Bool))
      (state-keys-flag (Maybe Bool)))))

(define-fun project-State_Indcpamod0_keys_top ((in State_Indcpamod0_inst_keys_top)) State_keys
  (mk-state-keys (state-Indcpamod0_inst-keys_top-T    in)
                 (state-Indcpamod0_inst-keys_top-z    in)
                 (state-Indcpamod0_inst-keys_top-flag in)))



(define-fun project-keys-State_Indcpamon0_indcpamon0 ((in CompositionState-Indcpamon0_inst)) State_keys
(let ((red-state (composition-pkgstate-Indcpamon0_inst-red        in))
      (ind-state (composition-pkgstate-Indcpamon0_inst-indcpamon0 in))
     )
(let ((ka    (state-Indcpamon0_inst-red-k        red-state))
      (kina  (state-Indcpamon0_inst-indcpamon0-k ind-state))
      (z     (state-Indcpamon0_inst-red-z        red-state))
      (flag  (state-Indcpamon0_inst-red-flag     red-state)))
(let ((Z (ite (or (not (= ka   (as mk-none (Maybe Bits_n))))
                  (not (= kina (as mk-none (Maybe Bits_n))))
              )
              (mk-some (store (store
                 ;initialize empty table 
                 ((as const (Array Bool (Maybe Bits_n))) (as mk-none (Maybe Bits_n))) 
                      (maybe-get z)  ka) 
                 (not (maybe-get z)) kina))
                 (as mk-none (Maybe (Array Bool (Maybe Bits_n))))
)))
     (mk-state-keys Z z flag)))))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Maybe (Array Bool (Maybe Bits_n))))) Bool
    (or
      (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get T) b) (as mk-none (Maybe Bits_n))
    )
))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

; T = none or for b=0,1: T b != none
(well-defined T)

;flag is either none or true
(or
    (= flag (as mk-none (Maybe Bool)))
    (= flag (   mk-some        true)))

;flag = true <=> T != none
(=
     (= flag (mk-some true))
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
)

;flag = true => z != none
(=>
     (= flag (mk-some true))
(not (= z (as mk-none (Maybe Bool)))))
)

))

; captures the possible states which a Key package can be in when
; the "top" queries are GETA and SETBIT queries 
;
(define-fun well-defined-Key-active ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(and
(or
  (= flag (as mk-none (Maybe Bool)))
  (= flag (   mk-some        true )))

 ;flag has been set  => bit has been set
(=> (=  (mk-some true ) flag)  
                    (or (=  (mk-some true ) z)
                        (=  (mk-some false) z)
                    ))
; key has been set => flag has been set
(=> (not            (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= flag (mk-some true)))
))))

(define-fun well-defined-Key-debug ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

(and true

;T != none or for b=0,1 T b != none
(well-defined T)
(not (= T (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
(not (= z (as mk-none (Maybe Bool))))
(= flag (mk-some true))

)))


;;;;;;;;;;;;;;;;;
;
; left  = mod
; right = mon
;
;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun randomness-mapping-SETBIT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int))         
         Bool
false
)


(define-fun randomness-mapping-GETAOUT (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool

;
; mon = right
; red samples with index 4 k_ ~ z
; SMP verwendet counter 1 to sample k_ ~ not z
;
; mod = left
; top key package samples r with index 1 for true
;                        rr with index 2 for false
;

(and
(=>
; if z = true
(=
; z

(state-Indcpamon0_inst-red-z
  (composition-pkgstate-Indcpamon0_inst-red 
    game-state-Indcpamon0_inst-old))
(mk-some true))

; then
(or

;(=  randval-left-GETA-1  ; r at true
;    randval-right-GETA-4 ; k_ at z=true
;)

(and     (= id-mod 1) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)

;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-1 ; k_ at not z = false
;)

(and     (= id-mod 2) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mon new-mon)
)))

(=>
; if z = false
(=
; z
(state-Indcpamon0_inst-red-z
(composition-pkgstate-Indcpamon0_inst-red
game-state-Indcpamon0_inst-old)) 
(mk-some false))

; then
(or
(and     (= id-mod 1) 
         (= id-mon 1) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
(and     (= id-mod 2) 
         (= id-mon 4) 
         (= ctr-mod new-mod)
         (= ctr-mod new-mod)
)
;(=  randval-left-GETA-1 ; r at true
;   randval-right-GETA-1 ; k_ at not z
;)
;(=  randval-left-GETA-2 ; rr at false
;   randval-right-GETA-4 ; k_ at z
;)
)
)
)
)

(define-fun randomness-mapping-GETKEYSIN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) 
        Bool
false
)

(define-fun randomness-mapping-ENCN (
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)
) Bool

(ite
(=
; z
(state-Indcpamon0_inst-red-z
(composition-pkgstate-Indcpamon0_inst-red
game-state-Indcpamon0_inst-old)) 
(mk-some arg-ENCN-d))
(and
(= id-mod 5)
(= id-mon 5)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)
(and
(= id-mod 5)
(= id-mon 2)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)
))

(define-fun randomness-mapping-ENCM (
;(= randval-left-ENCN-6 randval-right-ENCN-3)
        (ctr-mod     Int)
        (ctr-mon     Int) 
        (id-mod      Int)
        (id-mon      Int) 
        (new-mod Int)
        (new-mon Int)) Bool
(and
(= id-mod 6)
(= id-mon 3)
(= ctr-mod new-mod)
(= ctr-mon new-mon)
)        
)





;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun invariant-ENCN
        ((state-left  CompositionState-Indcpamod0_inst)
	 (state-right CompositionState-Indcpamon0_inst))
    Bool
  (let ((top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0_inst-keys_top state-left)))
        (top-key-package-right (project-keys-State_Indcpamon0_indcpamon0     state-right)))
    (and
      ;top key package states are equal
      (= top-key-package-left top-key-package-right)

      ;top key package state is "good"
      (well-defined-Key-debug top-key-package-left )
      (well-defined-Key-debug top-key-package-right)

      ;the functions left and right are the same
      (forall ((k Bits_n)(x Bits_n)(r Bits_n))
        (= (__func-Indcpamon0_inst-encn k x r) (__func-Indcpamod0_inst-encn  k x r))))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant stuff
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun invariant-SETBIT      (
        (state-left  CompositionState-Indcpamod0_inst )
        (state-right CompositionState-Indcpamon0_inst)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0_inst-keys_top     state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0   state-right ))  ;((;;(composition-pkgstate-Indcpamon0_inst-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))




(define-fun invariant-GETAOUT      (
        (state-left  CompositionState-Indcpamod0_inst )
        (state-right CompositionState-Indcpamon0_inst)
        ;(state-left-new  Return-Indcpamod0_inst-keys_top-GETAOUT)
        ;(state-right-new Return-Indcpamon0_inst-red-GETAOUT)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Indcpamod0_keys_top      (composition-pkgstate-Indcpamod0_inst-keys_top      state-left )))
(top-key-package-right (project-keys-State_Indcpamon0_indcpamon0  state-right )) ;  (((composition-pkgstate-Indcpamon0_inst-indcpamon0    (select state-right state-length-right))))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)


;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

)))







;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    aborts equal
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal-ENCN          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-enc-ENCN)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(= (= (return-Indcpamod0_inst-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m)))
   (= (return-Indcpamon0_inst-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m)))))



(define-fun aborts-equal-SETBIT          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-keys_top-SETBIT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool


(= (= (return-Indcpamod0_inst-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty)))
   (= (return-Indcpamon0_inst-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty)))))

(define-fun aborts-equal-GETAOUT          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-keys_top-GETAOUT)      ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-GETAOUT)          ; also contains new index
        )
        Bool



(= (= (return-Indcpamod0_inst-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n)))
   (= (return-Indcpamon0_inst-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n)))))



; no-abort

(define-fun no-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool


(and (not (= (return-Indcpamod0_inst-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))
     (not (= (return-Indcpamon0_inst-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))))


(define-fun left-abort-ENCN          (
        (state-left   CompositionState-Indcpamod0_inst)
        (state-right  CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool

(= (return-Indcpamod0_inst-enc-ENCN-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_m))))

(define-fun right-abort-ENCN          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-enc-ENCN)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-ENCN) ; also contains new index
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(= (return-Indcpamon0_inst-red-ENCN-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_m))))


(define-fun no-abort-SETBIT          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-keys_top-SETBIT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-SETBIT) ; also contains new index
        (zz Bool))
        Bool

(and (not (= (return-Indcpamod0_inst-keys_top-SETBIT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Empty))))
     (not (= (return-Indcpamon0_inst-red-SETBIT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Empty))))))

(define-fun no-abort-GETAOUT          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-GETAOUT) ; also contains new index
        )
        Bool

(and (not (= (return-Indcpamod0_inst-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))
     (not (= (return-Indcpamon0_inst-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))))


(define-fun left-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0_inst)
        (state-right  CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamod0_inst-keys_top-GETAOUT-return-value-or-abort     state-left-NEU) (as mk-abort (ReturnValue Bits_n))))


(define-fun right-abort-GETAOUT          (
        (state-left   CompositionState-Indcpamod0_inst)
        (state-right  CompositionState-Indcpamon0_inst)
        (state-left-NEU  Return-Indcpamod0_inst-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Indcpamon0_inst-red-GETAOUT) ; also contains new index
        )
        Bool

(= (return-Indcpamon0_inst-red-GETAOUT-return-value-or-abort     state-right-NEU) (as mk-abort (ReturnValue Bits_n))))




;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamod0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    State lemmas Indcpamon0
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output 
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;



(define-fun same-output-ENCN          (
        (state-left CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-enc-ENCN)
        (state-right-NEU Return-Indcpamon0_inst-red-ENCN)
        (d Bool)
        (nzero Bits_n)
        (none  Bits_n))
        Bool
(=
(return-Indcpamod0_inst-enc-ENCN-return-value-or-abort return-Indcpamod0_inst-ENCN)
(return-Indcpamon0_inst-red-ENCN-return-value-or-abort return-Indcpamon0_inst-ENCN)
)
)


(define-fun same-output-SETBIT          (
        (state-left  CompositionState-Indcpamod0_inst)
        (state-right CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-keys_top-SETBIT)
        (state-right-NEU Return-Indcpamon0_inst-red-SETBIT)
        (zz Bool))
        Bool
(=
(return-Indcpamod0_inst-keys_top-SETBIT-return-value-or-abort return-Indcpamod0_inst-SETBIT)
(return-Indcpamon0_inst-red-SETBIT-return-value-or-abort return-Indcpamon0_inst-SETBIT)
)
)

(define-fun same-output-GETAOUT          (
        (state-left   CompositionState-Indcpamod0_inst)
        (state-right  CompositionState-Indcpamon0_inst)
        (state-left-NEU Return-Indcpamod0_inst-keys_top-GETAOUT)
        (state-right-NEU Return-Indcpamon0_inst-red-GETAOUT)
        )
        Bool
(=
(return-Indcpamod0_inst-keys_top-GETAOUT-return-value-or-abort return-Indcpamod0_inst-GETAOUT)
(return-Indcpamon0_inst-red-GETAOUT-return-value-or-abort return-Indcpamon0_inst-GETAOUT)
)
)
