(define-package-invariant
(forall ((i Int) (b Bool))
                    (=> (not (is-mk-none (select pkg.T i)))
                    (not (is-mk-none (select (maybe-get (select pkg.T i)) b))))))