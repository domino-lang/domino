(define-package-invariant
   (and 
      (forall ((kid Int))
            (and
             (= (or (> kid pkg.kid_) (<= kid 0))
                (is-mk-none (select pkg.H kid))
                (is-mk-none (select pkg.LTK kid)))
             ))
      (>= pkg.kid_ 0)))
