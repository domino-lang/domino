The context imports c.f and c.g share Cell x on the left but use separate Cells x and y
on the right, all with offset 0. Expected: rejection with a context instance mismatch.
Eval() initializes both paths to 0, writes 1 through f, then reads g, returning 1 on the left and 0 on the right.
