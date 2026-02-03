; layer handle:
(declare-const handle Int)

; possible input for SETBIT
(declare-const bit Bool)

; possible input for GBLG     oracle GBLG(h: Integer, l: Integer, r: Integer, op: fn Bool,Bool -> Bool, j: Integer) -> Table(Bits(p),Bool) {
(declare-const l Int)
(declare-const r Int)
(declare-const op (Array (Tuple2 Bool Bool) (Maybe Bool)))
(declare-const j Int)

; possible state
(declare-const state-left-old CompositionState-Left)
(declare-const state-right-old CompositionState-Right)
(declare-const state-left-new CompositionState-Left)
(declare-const state-right-new CompositionState-Right)

; return value for GBLG call
(declare-const return-left Return_Left_gate_GBLG)
(declare-const return-right Return_Right_simgate_GBLG)
(declare-const is-abort-left Bool)
(declare-const is-abort-right Bool)
(declare-const value-left (Array Bits_p (Maybe Bool)))
(declare-const value-right (Array Bits_p (Maybe Bool)))

; sampled value Z and associated values
(declare-const Z-left  (Array Bool (Maybe Bits_n)))
(declare-const Z-right (Array Bool (Maybe Bits_n)))
(declare-const ctr-r-left Int)
(declare-const ctr-r-right Int)
(declare-const ctr-rr-left Int)
(declare-const ctr-rr-right Int)
(declare-const ctr-r-left-new Int)
(declare-const ctr-r-right-new Int)
(declare-const ctr-rr-left-new Int)
(declare-const ctr-rr-right-new Int)
(declare-const r-left Bits_n)
(declare-const r-right Bits_n)
(declare-const rr-left Bits_n)
(declare-const rr-right Bits_n)

(declare-const table-top-left-old     (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-left-new     (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-left-old  (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-left-new  (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-right-old    (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-top-right-new    (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-right-old (Array Int (Maybe (Array Bool (Maybe Bits_n)))))
(declare-const table-bottom-right-new (Array Int (Maybe (Array Bool (Maybe Bits_n)))))


(assert (and  ;assignment of return (value,state)
              (= return-left      (oracle-Left-gate-GBLG state-left-old handle l r op j))
              (= return-right     (oracle-Right-simgate-GBLG state-right-old handle l r op j))

              ;assignment of return values
              (= value-left       (return-Left-gate-GBLG-value return-left))
              (= value-right      (return-Right-simgate-GBLG-value return-right))

              ;assignment of abort values
              (= is-abort-left    (= mk-abort-Left-gate-GBLG return-left))
              (= is-abort-right   (= mk-abort-Right-simgate-GBLG return-right))

              ;assignment of return state
              (= state-left-new   (return-Left-gate-GBLG-state return-left))
              (= state-right-new  (return-Right-simgate-GBLG-state return-right))

              ;assignment of the ctr of the sample instructions for the lower Key package
              (= ctr-r-left   (composition-rand-Left-3  state-left-old))
              (= ctr-r-right  (composition-rand-Right-3 state-right-old))
              (= ctr-rr-left  (composition-rand-Left-4  state-left-old))
              (= ctr-rr-right (composition-rand-Right-4 state-right-old))

              ;assignment of the ctr of the sample instructions for the lower Key package on new state
              (= ctr-r-left-new   (composition-rand-Left-3  state-left-new))
              (= ctr-r-right-new  (composition-rand-Right-3 state-right-new))
              (= ctr-rr-left-new  (composition-rand-Left-4  state-left-new))
              (= ctr-rr-right-new (composition-rand-Right-4 state-right-new))

              ;assignment of the sampled values for the lower Key package
              (= r-left   (__sample-rand-Left-Bits_n 3 ctr-r-left))
              (= r-right  (__sample-rand-Right-Bits_n 3 ctr-r-right))
              (= rr-left  (__sample-rand-Left-Bits_n 4 ctr-rr-left))
              (= rr-right (__sample-rand-Right-Bits_n 4 ctr-rr-left))

              ;assignment of the sampled values for the lower Key package as a table
              (=  r-left  (maybe-get (select Z-left    true)))
              (= rr-left  (maybe-get  (select Z-left  false)))
              (= r-right  (maybe-get  (select Z-right  true)))
              (= rr-right (maybe-get (select Z-right  false)))

              ;variable for the state of the upper/lower key package left/right before/after call
              (= table-top-left-new   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-new)))
              (= table-top-right-new (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-new)))
              (= table-bottom-left-new   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-new)))
              (= table-bottom-right-new (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-new)))
              (= table-top-left-old   (state-Left-keys_top-T    (composition-pkgstate-Left-keys_top     state-left-old)))
              (= table-top-right-old (state-Right-keys_top-T    (composition-pkgstate-Right-keys_top    state-right-old)))
              (= table-bottom-left-old   (state-Left-keys_bottom-T (composition-pkgstate-Left-keys_bottom  state-left-old)))
              (= table-bottom-right-old (state-Right-keys_bottom-T (composition-pkgstate-Right-keys_bottom state-right-old)))


))

(check-sat) ;2
; At each entry, the table is either none or a total table
(define-fun well-defined ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))) Bool
  (forall ((h Int))
    (ite
      (not
        (= (select T h) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T h)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )
)

(declare-const hhh Int)
(define-fun well-defined-ish ((T (Array Int (Maybe (Array Bool (Maybe Bits_n)))))(hhh Int)) Bool
    (ite
      (not
        (= (select T hhh) (as mk-none (Maybe (Array Bool (Maybe Bits_n)))))
      )
      (forall ((b Bool))
        (not
          (= (select (maybe-get (select T hhh)) b) (as mk-none (Maybe Bits_n)))
        )
      )
      true
    )
  )


(check-sat) ;3
(declare-const precondition-holds Bool)
(assert (= precondition-holds (and

;;;;;;Pre-condition (part of the invariant):

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-old)
(well-defined table-top-right-old)
(well-defined table-bottom-left-old)
(well-defined table-bottom-right-old)

;top/bottom key packages left and right are equal (before the call)
(= table-top-left-old table-top-right-old)
(= table-bottom-left-old table-bottom-right-old)

;The randomness ctr left and right are equal (before the call)
(= ctr-r-left ctr-r-right)
(= ctr-rr-left ctr-rr-right)

;;;;;;Pre-condition (randomness mapping):
;equality of values of the sample instructions for the lower Key package
(= r-left r-right)
(= rr-left rr-right)

;;;;;; Pre-condition "Glue" 

;op is a total table.
;op is a total table.
(not (= (select op (mk-tuple2 true  true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 true  false))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false true ))(as mk-none (Maybe Bool))))
(not (= (select op (mk-tuple2 false false))(as mk-none (Maybe Bool))))

)))

(check-sat) ;4
(declare-const lemmas-hold Bool)
(declare-const lemma1 Bool)
(declare-const lemma2 Bool)
(declare-const lemma3 Bool)
(declare-const lemma4 Bool)
(declare-const lemma5 Bool)

(assert (= lemmas-hold (and
lemma1
lemma2
lemma3
lemma4
lemma5)))

(assert (= lemma1 (and
;;;; Lemma on key tables
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined-ish table-bottom-left-new hhh)
(well-defined-ish table-bottom-right-new hhh)
)))

(declare-const debug-top-left Bool)
(declare-const debug-top-right Bool)
(declare-const debug-bottom-left Bool)
(declare-const debug-bottom-right Bool)

(assert 
(and
(= (well-defined table-top-left-new) debug-top-left)
(= (well-defined table-top-right-new) debug-top-right)
(= (well-defined table-bottom-left-new) debug-bottom-left)
(= (well-defined table-bottom-right-new) debug-bottom-right)
))





(assert (= lemma2 (and
; top tables remain the same
(= table-top-left-old table-top-left-new)
(= table-top-right-old table-top-right-new)
)))

(assert (= lemma3 (and
; left: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(= handle hh)
(= (maybe-get (select table-bottom-left-new hh)) Z-left)
(= (select table-bottom-left-old hh) (select table-bottom-left-new hh))
))
)))

;(declare-const hhh Int)

(assert (= lemma4 (and
; right: bottom tables are mostly equal and where they are not equal, there is Z
(forall ((hh Int))
(ite
(= handle hh)
(= (maybe-get (select table-bottom-right-new hh)) Z-right)
(= (select table-bottom-right-old hh) (select table-bottom-right-new hh))
))
))
)

(check-sat) ;5

(declare-const postcondition-holds Bool)
(assert (= postcondition-holds (and

;All tables in the key packages are either completely defined or completely undefined, left, right, top, bottom
(well-defined table-top-left-new)
(well-defined table-top-right-new)
(well-defined table-bottom-left-new)
(well-defined table-bottom-right-new)

;top/bottom key packages left and right are equal (before the call)
(= table-top-left-old table-top-right-new)
(= table-bottom-left-old table-bottom-right-new)

;The randomness ctr left and right are equal (before the call)
(= ctr-r-left-new ctr-r-right-new)
(= ctr-rr-left-new ctr-rr-right-new)

)))

(check-sat) ;6
(declare-const standard-postcondition-holds Bool)
(assert (= standard-postcondition-holds 
            (and
            (= is-abort-right is-abort-left)
            (or 
            is-abort-left
            (= value-left value-right)
            )
            )
        )
)

(check-sat) ;7

;;;;;;;;;;;;; temp
(push 1)

(assert precondition-holds)
(check-sat) ;8

(pop 1)

(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma4)))
(check-sat) ;9
;(get-model)
(pop 1)





(push 1)

(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma3)))
(check-sat) ;10
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma2)))
(check-sat) ;11
;(get-model)
(pop 1)

(push 1)
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemma1)))
(check-sat) ;12
(get-model)
(pop 1)

(push 1)


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;;
;; end of temp
;;
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;


;missing:
;precondition holds on starting state
;pre-condition => lemmas
(assert (and precondition-holds
             (not is-abort-right)
             (not is-abort-left)
             (not lemmas-hold)))


(check-sat) ;13
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => post-condition
(assert (and precondition-holds
             lemmas-hold
             (not is-abort-right)
             (not is-abort-left)
             (not postcondition-holds)))

(check-sat) ;14
;(get-model)
(pop 1)

(push 1)

;pre-condition + lemmas => standard post-condition
(assert (and precondition-holds 
             lemmas-hold
             (not standard-postcondition-holds)))
(check-sat) ;15
;(get-model)
(pop 1)

(push 1)
