(define-state-relation invariant
    (state-left state-right)
    (and
        (= state-left.Keys.WireKey state-right.LayeredKeys.WireKey)
        (= state-left.Keys.ActiveBit state-right.LayeredKeys.ActiveBit)
    )
)

