; Story 42: one relation per translation case.

(define-state-relation dotted-state (left right)
  (= left.Store.ctr right.Keep.ctr))

(define-state-relation dotted-param (left right)
  (= left.Front.b right.Front.b))

(define-state-relation same-package-with-state (state-left state-right)
  (= state-left.T state-right.T))

(define-state-relation same-package-stateless (state-left state-right)
  (= state-left.Front state-right.Front))
