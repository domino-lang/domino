(define-package-invariant
  (and
    (>= pkg.ctr 0)
    (forall ((i Int))
      (=> (or (< i 0) (>= i pkg.ctr))
          (is-mk-none (select pkg.seen i))))))
