The assumption games both export Eval, backed by RealEval of r and IdealEval of i.
The same context calls RealEval of real on the left and IdealEval of ideal on the right.
The mappings identify r with real and i with ideal, so both context wires enter Eval.
Expected: the reduction accepts despite the different internal oracle names.
