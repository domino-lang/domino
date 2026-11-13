The right construction swaps router.f and router.g between x.O1 and x.O2;
both mapped assumption games and the left retain the original wiring.
Expected: rejection with `domino::code::theorem::reduction::mapping::wiring_mismatch`
and reason `import or destination oracle name differs`.
Eval() returns O1()-O2() = -1 on the left but O2()-O1() = 1 on the right.
