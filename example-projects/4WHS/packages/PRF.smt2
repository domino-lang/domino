(define-package-invariant
    (forall ((kid Int))
            (= (> kid pkg.kid_)
               (and (is-mk-none (select pkg.H kid))
                    (is-mk-none (select pkg.LTK kid))))))
