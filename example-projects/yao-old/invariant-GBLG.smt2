
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Randomness mapping
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(define-fun randomness-mapping-GBLG (
        (ctr-left      Int)
        (ctr-right     Int) 
        (id-left       Int)
        (id-right      Int) 
        (new-left      Int)
        (new-right     Int)
                                    ) Bool
(or
(and
(= ctr-left  new-left )
(= ctr-right new-right)
(= id-left  5)
(= id-right 7)
)
(and
(= ctr-left  new-left )
(= ctr-right new-right)
(= id-left  6)
(= id-right 8)
)
(and
(= ctr-left  new-left )
(= ctr-right new-right)
(= id-left  9)
(= id-right 9)
)
(and
(= ctr-left  new-left )
(= ctr-right new-right)
(= id-left  11)
(= id-right 10)
)
(and
(= (+ 1 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  9)
(= id-right 11)
)
(and
(= (+ 1 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  11)
(= id-right 12)
)
(and
(= (+ 2 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  9)
(= id-right 13)
)
(and
(= (+ 2 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  11)
(= id-right 14)
)
(and
(= (+ 3 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  9)
(= id-right 15)
)
(and
(= (+ 3 ctr-left)  new-left )
(= ctr-right new-right)
(= id-left  11)
(= id-right 16)
)
)
;equality of values of the sample functions for the lower Key package
;(= randval-left-5    randval-right-7)
;(= randval-left-6    randval-right-8)

;equality of values of the sample functions for the encryptions
;(= randval-left-9    randval-right-9)
;(= randval-left-11   randval-right-10)
;(= randval-left-9+1  randval-right-11)
;(= randval-left-11+1 randval-right-12)
;(= randval-left-9+2  randval-right-11)
;(= randval-left-11+2 randval-right-12)
;(= randval-left-9+3  randval-right-13)
;(= randval-left-11+3 randval-right-14)
;)
)

(define-fun randomness-mapping-SETBIT (
        (ctr-left      Int)
        (ctr-right     Int) 
        (id-left       Int)
        (id-right      Int) 
        (new-left      Int)
        (new-right     Int)
) Bool
false
)

(define-fun randomness-mapping-GETAOUT (
        (ctr-left      Int)
        (ctr-right     Int) 
        (id-left       Int)
        (id-right      Int) 
        (new-left      Int)
        (new-right     Int)
) Bool
(or
(and
(= id-left  1)
(= id-right 1)
(= ctr-left  new-left )
(= ctr-right new-right)
)
(and
(= id-left  2)
(= id-right 2)
(= ctr-left  new-left )
(= ctr-right new-right)
))
;(and
;(= randval-left-GETA-1 randval-right-GETA-1)
;(= randval-left-GETA-2 randval-right-GETA-2)
;)
)

(define-fun randomness-mapping-GETKEYSIN (
        (ctr-left      Int)
        (ctr-right     Int) 
        (id-left       Int)
        (id-right      Int) 
        (new-left      Int)
        (new-right     Int)
) 
Bool
false
)



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   op is total (special-purpose glue)
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(assert
(and
(not (= (select arg-GBLG-op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select arg-GBLG-op (mk-tuple2 false false))(as mk-none (Maybe Bool))))
))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Datatypes to extract key package state
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


(declare-datatype
  State_keys
  (
    (mk-state-keys
      (state-keys-T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
      (state-keys-z (Array Int (Maybe Bool)))
      (state-keys-flag (Array Int (Maybe Bool))))))

(define-fun project-State_Left_inst-_keys_top ((in State_Left_inst-_keys_top)) State_keys
  (mk-state-keys (state-Left_inst--keys_top-T    in)
                 (state-Left_inst--keys_top-z    in)
                 (state-Left_inst--keys_top-flag in)))

(define-fun project-State_Right_inst-_keys_top ((in State_Right_inst-_keys_top)) State_keys
  (mk-state-keys (state-Right_inst--keys_top-T    in)
                 (state-Right_inst--keys_top-z    in)
                 (state-Right_inst--keys_top-flag in)))

(define-fun project-State_Left_inst-_keys_bottom ((in State_Left_inst-_keys_bottom)) State_keys
  (mk-state-keys (state-Left_inst--keys_bottom-T    in)
                 (state-Left_inst--keys_bottom-z    in)
                 (state-Left_inst--keys_bottom-flag in)))

(define-fun project-State_Right_inst-_keys_bottom ((in State_Right_inst-_keys_bottom)) State_keys
  (mk-state-keys (state-Right_inst--keys_bottom-T    in)
                 (state-Right_inst--keys_bottom-z    in)
                 (state-Right_inst--keys_bottom-flag in)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;   Well-definedness of tables
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;If T h != none => T h b != none (for both b=0 and b=1)

(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (or
      (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
)))))

; captures the possible states which a Key package can be in when
; the "top" queries are GETKEYS queries 
;
(define-fun well-defined-Key-bool ((key-state State_keys)) Bool
(let ((T    (state-keys-T    key-state))
      (flag (state-keys-flag key-state))
      (z    (state-keys-z    key-state)))

; flag is true <=> key has been chosen 
(and

;If T h != none => T h b != none (for both b=0 and b=1)
(well-defined T)

(forall ((hhh Int))
(or
    (= (select flag hhh) (as mk-none (Maybe Bool)))
    (= (select flag hhh) (   mk-some        true )))
)

;If flag h != true => T h  = none
;If flag h  = true => T h != none (for both b=0 and b=1)

(forall ((hhh Int)) 
(and 
(=>
    (not (= (select flag hhh) (mk-some true)))
    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
)
(=>
    (= (select flag hhh) (mk-some true))
    (and
       (not (= (select T hhh)                            (as mk-none (Maybe (Array Bool (Maybe Bits_n))))))
       (not (= (select (maybe-get (select T hhh)) true ) (as mk-none (Maybe Bits_n))))
       (not (= (select (maybe-get (select T hhh)) false) (as mk-none (Maybe Bits_n))))
    )
))))))

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

(forall ((hhh Int))
(or
  (= (select flag hhh) (as mk-none (Maybe Bool)))
  (= (select flag hhh) (   mk-some        true ))))

; flag has been set  => bit has been set
(forall ((hhh Int)) (=> (=  (mk-some true ) (select flag hhh))  
                    (or (=  (mk-some true ) (select z    hhh))
                        (=  (mk-some false) (select z    hhh))
                    )))

; key has been set => flag has been set
(forall ((hhh Int)) (=>
                    (not
                    (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
                    )
                    (= (select flag hhh) (mk-some true)))
                    ))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Invariant
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


; This is supposed to be an invariant
(define-fun invariant-GBLG          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left  Int) ;old index
;        (state-length-right Int) ;old index
;        (state-left-new  Return-Left-gate-GBLG)
;        (state-right-new Return-Right-simgate-GBLG)
;        (h Int)
;        (l Int)
;        (r Int)
;        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
;        (j Int)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_keys_top      (composition-pkgstate-Left-keys_top     state-left )))
(top-key-package-right (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top    state-right)))
(bot-key-package-left  (project-State_Left_keys_bottom   (composition-pkgstate-Left-keys_bottom  state-left )))
(bot-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom state-right)))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))


(define-fun invariant-SETBIT      (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left  Int) ;old index
;        (state-length-right Int) ;old index
;        (state-left-new  Return_Left_keys_top_SETBIT)
;        (state-right-new Return_Right_keys_top_SETBIT)
;        (h Int)
;        (zz Bool)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_keys_top      (composition-pkgstate-Left-keys_top     state-left  )))
(top-key-package-right (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top    state-right )))
(bot-key-package-left  (project-State_Left_keys_bottom   (composition-pkgstate-Left-keys_bottom  state-left  )))
(bot-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom state-right )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))



(define-fun invariant-GETAOUT      (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left  Int) ;old index
;        (state-length-right Int) ;old index
;        (state-left-new  Return_Left_keys_top_GETAOUT)
;        (state-right-new Return_Right_keys_top_GETAOUT)
;        (h Int)
        )
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_keys_top      (composition-pkgstate-Left-keys_top     state-left )))
(top-key-package-right (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top    state-right)))
(bot-key-package-left  (project-State_Left_keys_bottom   (composition-pkgstate-Left-keys_bottom  state-left )))
(bot-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom state-right)))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))



(define-fun invariant-GETKEYSIN      (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left  Int) ;old index
;        (state-length-right Int) ;old index
;        (state-left-new  Return_Left_keys_bottom_GETKEYSIN)
;        (state-right-new Return_Right_keys_bottom_GETKEYSIN)
;        (h Int)
)
    Bool
    (let

; state of the key packages
(
(top-key-package-left  (project-State_Left_keys_top      (composition-pkgstate-Left-keys_top     state-left  )))
(top-key-package-right (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top    state-right )))
(bot-key-package-left  (project-State_Left_keys_bottom   (composition-pkgstate-Left-keys_bottom  state-left  )))
(bot-key-package-right (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom state-right )))
)

(let

; table of the bottom key package
(
(table-bot-left  (state-keys-T    bot-key-package-left))
(table-bot-right (state-keys-T    bot-key-package-right))
(    z-bot-left  (state-keys-z    bot-key-package-left))
(    z-bot-right (state-keys-z    bot-key-package-right))
(flag-bot-left   (state-keys-flag bot-key-package-left))
(flag-bot-right  (state-keys-flag bot-key-package-right))
)

(and
;top key package states are equal
(= top-key-package-left top-key-package-right)

;for bottom key package, tables are equal
(= table-bot-left table-bot-right)

;top key package state is "good"
(well-defined-Key-active top-key-package-left )
(well-defined-Key-active top-key-package-right)

;bottom key packages state is "good"
(well-defined-Key-bool   bot-key-package-left )
(well-defined-Key-active bot-key-package-right)
(forall ((h Int))
(and
    (= (select  flag-bot-left  h) 
       (select  flag-bot-right h))
(=> (= (select table-bot-left  h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (= (select  flag-bot-left  h) (   mk-some        false)))
(=> (= (select table-bot-right h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
    (and
    (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool )))))
(=> (= (select  flag-bot-right h) (   mk-some        false))
    (= (select     z-bot-right h) (as mk-none (Maybe Bool ))))
))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    LEFT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun left-all-aborts          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left Int)  ; old index
;        (state-length-right Int) ; old index
        (state-left-NEU  Return-Left-gate-GBLG)      
        (state-right-NEU Return-Right-simgate-GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (return-Left-gate-GBLG-game-state state-left-NEU)
      )
         )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Left_inst-_keys_top     (composition-pkgstate-Left_inst--keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Left_inst-_keys_bottom  (composition-pkgstate-Left_inst--keys_bottom  state-left-1)))
)

(let

; table of the top key package
;        T: Table(Integer,Table(Bool,Bits(n))),
;        z: Table(Integer,Bool),
(
(T-top-left-1        (state-keys-T       top-key-package-left-1))
(z-top-left-1        (state-keys-z       top-key-package-left-1))
(flag-top-left-1     (state-keys-flag    top-key-package-left-1))
(flag-bot-left-1     (state-keys-flag bottom-key-package-left-1))
)

;;; if l is undefined, then abort
(=>
(or
(= (select    z-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l)    (mk-some        false))
(= (select    z-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r)    (mk-some        false))
(= (select flag-bot-left-1 j)    (mk-some        true ))
)
;(= (return-Left-gate-GBLG-is-abort state-left-NEU) true)
;
; in der neuen match syntax below:
;
(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort true)
 ((mk-return-value v) false)))
)))))

; re-built this:

(define-fun left-inverse-all-aborts          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left Int)  ; old index
;        (state-length-right Int) ; old index
        (state-left-NEU  Return-Left-gate-GBLG)      
        (state-right-NEU Return-Right-simgate-GBLG) 
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


    (let (
      (state-left-1  (return-Left-gate-GBLG-game-state state-left-NEU)
      )
         )

  (let

; state of the key packages
(
(top-key-package-left-1     (project-State_Left_keys_top     (composition-pkgstate-Left-keys_top     state-left-1)))
(bottom-key-package-left-1  (project-State_Left_keys_bottom  (composition-pkgstate-Left-keys_bottom  state-left-1)))
)

(let

; table of the top key package
;        T: Table(Integer,Table(Bool,Bits(n))),
;        z: Table(Integer,Bool),
(
(T-top-left-1        (state-keys-T       top-key-package-left-1))
(z-top-left-1        (state-keys-z       top-key-package-left-1))
(flag-top-left-1     (state-keys-flag    top-key-package-left-1))
(flag-bot-left-1     (state-keys-flag bottom-key-package-left-1))
)

;;; if l is undefined, then abort
(=>
;(= (return-Left-gate-GBLG-is-abort state-left-NEU) true)
;
; in der neuen match syntax below:
;
(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort true)
 ((mk-return-value v) false)))
(or
(= (select    z-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 l)    (mk-some        false))
(= (select    z-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-left-1 r)    (mk-some        false))
(= (select flag-bot-left-1 j)    (mk-some        true ))
)
)))))



;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    RIGHT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; when ... happens, then abort

(define-fun right-all-aborts          (
        (state-left     CompositionState-Left )
        (state-right    CompositionState-Right)
;        (state-length-left Int)  ; old index
;        (state-length-right Int) ; old index
        (state-left-NEU  Return-Left-gate-GBLG)      ; old index
        (state-right-NEU Return-Right-simgate-GBLG) ; old index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom  state-right)))
(top-key-package-right-1       (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top     state-right)))
)


(let

; tables of the top and bottom key package
(
(   T-top-right-1  (state-keys-T       top-key-package-right-1))
(   z-top-right-1  (state-keys-z       top-key-package-right-1))
(flag-top-right-1  (state-keys-flag    top-key-package-right-1))
(flag-bot-right-1  (state-keys-flag bottom-key-package-right-1))
(   z-bot-right-1  (state-keys-z    bottom-key-package-right-1))
)

;;; if j is true, then abort, re-written as
;;; if no abort, then j is false
;(=>
;(= (return-Right-simgate-GBLG-is-abort state-right-NEU) true)
;(let ((outcome (get-outcome returnvalue)))
;  (match outcome
;    (( mk-abort  
;         (and (cond1 state)
;              (cond2 state)))
;     ((mk-return-value v) 
;         (and (cond1 state v) 
;              (cond2 state v))))))
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(((mk-return-value v)
(not
(or
(= (select    z-top-right-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 l) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 l)    (mk-some        false))
(= (select    z-top-right-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 r) (as mk-none (Maybe Bool)))
(= (select flag-top-right-1 r)    (mk-some        false))
(= (select flag-bot-right-1 j)    (mk-some        true ))
(= (select    z-bot-right-1 j)    (mk-some        true ))
(= (select    z-bot-right-1 j)    (mk-some        false))
))
)
(mk-abort true)
)))))



(define-fun right-all-aborts-inverse          (
        (state-left        CompositionState-Left )
        (state-right       CompositionState-Right)
       ; (state-length-left  Int) ; old index
       ; (state-length-right Int) ; old index
        (state-left-NEU     Return-Left-gate-GBLG)     ; contains own index
        (state-right-NEU    Return-Right-simgate-GBLG) ; contains own index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

  (let

; state of the key packages
(
(bottom-key-package-right-1    (project-State_Right_keys_bottom  (composition-pkgstate-Right-keys_bottom  state-right)))
(   top-key-package-right-1    (project-State_Right_keys_top     (composition-pkgstate-Right-keys_top     state-right)))
)


(let

; table of the bottom key package
(
(   T-top-right-1     (state-keys-T       top-key-package-right-1))
(   z-top-right-1     (state-keys-z       top-key-package-right-1))
(flag-top-right-1     (state-keys-flag    top-key-package-right-1))
(flag-bottom-right-1  (state-keys-flag bottom-key-package-right-1))
(   z-bottom-right-1  (state-keys-z    bottom-key-package-right-1))
)

;;; abort => input on l or z not defined or output was already defined.
;(=>
;(= (return-Right-simgate-GBLG-is-abort state-right-NEU) true)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
((mk-abort
(or
(= (select    z-top-right-1    l)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    l)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    l)       (mk-some        false))
(= (select    z-top-right-1    r)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    r)    (as mk-none (Maybe Bool)))
(= (select flag-top-right-1    r)       (mk-some        false))
(= (select flag-bottom-right-1 j)       (mk-some        true ))
(= (select    z-bottom-right-1 j)       (mk-some        true ))
(= (select    z-bottom-right-1 j)       (mk-some        false))
))
((mk-return-value v) true)
)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
;    LEFT aborts = RIGHT aborts
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun aborts-equal          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
       ; (state-length-left  Int) ; old index = 1
       ; (state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-gate-GBLG)      ; also contains new index    
        (state-right-NEU Return-Right-simgate-GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
;(= (return-Left-gate-GBLG-is-abort     state-left-NEU)
;   (return-Right-simgate-GBLG-is-abort state-right-NEU))

(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
))))))

(define-fun aborts-equal-SETBIT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-keys_top-SETBIT)      ; also contains new index    
        (state-right-NEU Return-Right-keys_top-SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool


(match (return-Left-keys_top-SETBIT-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_top-SETBIT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_top-SETBIT-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
)))))
)

(define-fun aborts-equal-GETAOUT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-keys_top-GETAOUT)      ; also contains new index    
        (state-right-NEU Return-Right-keys_top-GETAOUT) ; also contains new index
        (h Int))
        Bool


(match (return-Left-keys_top-GETAOUT-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_top-GETAOUT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_top-GETAOUT-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
)))))
;(= (return-Left-keys_top-GETAOUT-is-abort  state-left-NEU)
;   (return-Right-keys_top-GETAOUT-is-abort state-right-NEU))
)


(define-fun aborts-equal-GETKEYSIN          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-keys_bottom-GETKEYSIN)      ; also contains new index    
        (state-right-NEU Return-Right-keys_bottom-GETKEYSIN) ; also contains new index
        (h Int))
        Bool
(match (return-Left-keys_bottom-GETKEYSIN-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_bottom-GETKEYSIN-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_bottom-GETKEYSIN-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
)))))

;(= (return-Left-keys_bottom-GETKEYSIN-is-abort  state-left-NEU)
;   (return-Right-keys_bottom-GETKEYSIN-is-abort state-right-NEU))
)

(define-fun aborts-left-right          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-gate-GBLG)      ; also contains new index    
        (state-right-NEU Return-Right-simgate-GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool


(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            true) ;ex falso quod libet
 ((mk-return-value v)  true)
)))))

;(=> (return-Left-gate-GBLG-is-abort     state-left-NEU)
;    (return-Right-simgate-GBLG-is-abort state-right-NEU))
)

(define-fun aborts-right-left          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-gate-GBLG)      ; also contains new index    
        (state-right-NEU Return-Right-simgate-GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool

(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  true)
)))
 ((mk-return-value v)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            false) ;modus ponens
 ((mk-return-value v)  true)
)))))

;(=> (return-Right-simgate-GBLG-is-abort state-right-NEU)
;    (return-Left-gate-GBLG-is-abort     state-left-NEU ))
)


; no-abort

(define-fun no-abort          (
        (state-left  CompositionState-Left)
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU Return-Left-gate-GBLG)      ; also contains new index    
        (state-right-NEU Return-Right-simgate-GBLG) ; also contains new index
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
)))))
;(and
;(= (return-Left-gate-GBLG-is-abort     state-left-NEU)
;   false)
;(= (return-Right-simgate-GBLG-is-abort     state-right-NEU)
;   false)
;)
)

(define-fun no-abort-SETBIT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
       ; (state-length-left  Int) ; old index = 1
       ; (state-length-right Int) ; old index = 1
        (state-left-NEU  Return-Left-keys_top-SETBIT)  ; also contains new index    
        (state-right-NEU Return-Right-keys_top-SETBIT) ; also contains new index
        (h Int)
        (zz Bool))
        Bool
(match (return-Left-keys_top-SETBIT-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_top-SETBIT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_top-SETBIT-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
)))))
;(and
;(= (return-Left-keys_top-SETBIT-is-abort     state-left-NEU)
;   false)
;(= (return-Right-keys_top-SETBIT-is-abort     state-right-NEU)
;   false)
;)
)

(define-fun no-abort-GETAOUT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU  Return-Left-keys_top-GETAOUT)  ; also contains new index    
        (state-right-NEU Return-Right-keys_top-GETAOUT) ; also contains new index
        (h Int))
        Bool

(and
(match (return-Left-keys_top-GETAOUT-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_top-GETAOUT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_top-GETAOUT-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
))))))
;(= (return-Left-keys_top-GETAOUT-is-abort     state-left-NEU)
;   false)
;(= (return-Right-keys_top-GETAOUT-is-abort     state-right-NEU)
;   false)
)

(define-fun no-abort-GETKEYSIN          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left  Int) ; old index = 1
        ;(state-length-right Int) ; old index = 1
        (state-left-NEU  Return-Left-keys_bottom-GETKEYSIN)  ; also contains new index    
        (state-right-NEU Return-Right-keys_bottom-GETKEYSIN) ; also contains new index
        (h Int))
        Bool
(and
(match (return-Left-keys_bottom-GETKEYSIN-return-value-or-abort state-left-NEU)
((mk-abort
(match (return-Right-keys_bottom-GETKEYSIN-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value v)  false)
)))
 ((mk-return-value v)
(match (return-Right-keys_bottom-GETKEYSIN-return-value-or-abort state-right-NEU)
(( mk-abort            false)
 ((mk-return-value v)  true)
))))))
;(and
;(= (return-Left-keys_bottom-GETKEYSIN-is-abort     state-left-NEU)
;   false)
;(= (return-Right-keys_bottom-GETKEYSIN-is-abort     state-right-NEU)
;   false)
;)
)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;
; Same Output
;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define-fun same-output          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
        ;(state-length-left-old Int)
        ;(state-length-right-old Int)
        (state-left-NEU Return-Left-gate-GBLG)
        (state-right-NEU Return-Right-simgate-GBLG)
        (h Int)
        (l Int)
        (r Int)
        (op (Array (Tuple2 Bool Bool) (Maybe Bool)))
        (j Int))
        Bool
(and
(match (return-Left-gate-GBLG-return-value-or-abort state-left-NEU)
((mk-abort true)
((mk-return-value v)
(match (return-Right-simgate-GBLG-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value w)  (= v w))
))))))
;(=
;(return-Left-gate-GBLG-value return-left-gate-GBLG)
;(return-Right-simgate-GBLG-value return-right-simgate-GBLG)
;)
)

(define-fun same-output-SETBIT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left-old Int)
;        (state-length-right-old Int)
        (state-left-NEU Return-Left-keys_top-SETBIT)
        (state-right-NEU Return-Right-keys_top-SETBIT)
        (h Int)
        (zz Bool))
        Bool
(and
(match (return-Left-keys_top-SETBIT-return-value-or-abort state-left-NEU)
((mk-abort true)
((mk-return-value v)
(match (return-Right-keys_top-SETBIT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value w)  (= v w))
))))))
;(=
;(return-Left-keys_top-SETBIT-value return-left-keys_top-SETBIT)
;(return-Right-keys_top-SETBIT-value return-right-keys_top-SETBIT)
;)
)

(define-fun same-output-GETAOUT          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
       ; (state-length-left-old Int)
       ; (state-length-right-old Int)
        (state-left-NEU Return-Left-keys_top-GETAOUT)
        (state-right-NEU Return-Right-keys_top-GETAOUT)
        (h Int))
        Bool
(and
(match (return-Left-keys_top-GETAOUT-return-value-or-abort state-left-NEU)
((mk-abort true)
((mk-return-value v)
(match (return-Right-keys_top-GETAOUT-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value w)  (= v w))
))))))
;(=
;(return-Left-keys_top-GETAOUT-value return-left-keys_top-GETAOUT)
;(return-Right-keys_top-GETAOUT-value return-right-keys_top-GETAOUT)
;)
)

(define-fun same-output-GETKEYSIN          (
        (state-left  CompositionState-Left )
        (state-right CompositionState-Right)
;        (state-length-left-old Int)
;        (state-length-right-old Int)
        (state-left-NEU Return-Left-keys_bottom-GETKEYSIN)
        (state-right-NEU Return-Right-keys_bottom-GETKEYSIN)
        (h Int))
        Bool
(and
(match (return-Left-keys_bottom-GETKEYSIN-return-value-or-abort state-left-NEU)
((mk-abort true)
((mk-return-value v)
(match (return-Right-keys_bottom-GETKEYSIN-return-value-or-abort state-right-NEU)
(( mk-abort            true)
 ((mk-return-value w)  (= v w))
))))))
;(=
;(return-Left-keys_bottom-GETKEYSIN-value return-left-keys_bottom-GETKEYSIN)
;(return-Right-keys_bottom-GETKEYSIN-value return-right-keys_bottom-GETKEYSIN)
;)
)
