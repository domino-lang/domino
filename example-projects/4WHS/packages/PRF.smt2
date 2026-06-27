(define-package-invariant
    (forall ((kid Int))
            (and
             (= (> kid pkg.kid_)
                (is-mk-none (select pkg.H kid))
                (is-mk-none (select pkg.LTK kid)))
             (= (> kid pkg.kid_) ;; why is this needed?
                (and
                 (is-mk-none (select pkg.H kid))
                 (is-mk-none (select pkg.LTK kid)))))))
