# Story 19 follow-up — implementation report: early returns as `goto` in the HTML viewer

**Status:** done (requested in conversation). Branch `amir/html-viewer`, commits `0db5c7ff`
(goto) and `ab1140a2` (dead code after a return).

## 1. The problem

The HTML viewer inlines a callee into its caller (`debug::view::render_oracle_view`). The
callee's `return e` is printed as `bind <- e`. That is only right when the return is the last
statement the callee runs. `returnify` guarantees a return at the end of every path, but an
oracle can still return early from an `if`.

Until now the viewer arranged the tail position with a rewrite, `normalize`:

```
if c { … return x; } rest      ⟶      if c { … return x; } else { rest }
```

The rewrite only fires when a branch exits on every path. It never copies code. A return
nested in a branch that can fall through was left where it was:

```
if a {
  if b { return x; }     // normalize turns this into: if b { return x } else { s1 }
  s1;
}
s2;                      // still runs after `return x` on the page
return y;
```

A return inside a `for` was left as well. Such a return was printed as `y <- x;  // returns
from P.O`, so the early exit appeared only in a comment. Nothing in the example projects hit this
case, but the construction did not rule it out.

## 2. What the page shows now

`normalize` is gone, and inlined callees keep the shape of their source. A return the callee
can run before its last statement prints its assignment, followed by a jump to a label placed
right after the inlined body:

```
    // inlined Scheme_KEMDEM.DEC
        …
        if (k == None) {
            m <- None;
            goto end_Scheme_KEMDEM_DEC;  // returns from Scheme_KEMDEM.DEC
        }
        // inlined Scheme_DEM.DEM_DEC
            …
        m <- Some(m_2);
    end_Scheme_KEMDEM_DEC:
    return m;
```

- **Soundness.** The goto always targets the end of the frame the return belongs to, however
  deep the return sits in `if`s or `for` loops.
- **Labels.** A label is named `end_Instance_Oracle`, with characters other than letters and
  digits replaced by `_`. The label line sits at the `// inlined` comment's indentation. It is
  only printed when a goto uses it (`Frame::end`, a `OnceCell` filled by the first early
  return). A second inlining of the same oracle in one listing gets `end_P_O_2`, and so on
  (`View::labels`).
- **Tail returns** stay plain assignments. Returns of the entry oracle stay real `return`s.
- **Dead code.** `View::block` stops after a statement that always exits: a `return`, an
  `abort`, or an `if` whose remaining branches all exit (`View::exits`). Only branches that
  survive constant folding count. That statement ends the block, so a return in it keeps tail
  position. Without this, `Prf.Eval` in 4WHS `Hybrid2` (`b: false`, so the guard
  `(H[kid] == Some(false)) or not b` is true) printed `goto end_Prf_Eval;` followed by the ideal
  branch, which can never run. The old `normalize` had moved that code into the else branch,
  which folding then dropped. This also removes code after an unconditional return in the entry
  oracle.

## 3. Changes

| File | Change |
|---|---|
| `src/debug/view.rs` | Removed `normalize` and `exits_by_return`. `Frame::end` holds the label; `View::labels` and `View::end_label` hand out fresh names. `Statement::Return` emits `goto … // returns from P.O` when it is not in tail position. `View::call` prints the label after the body. `View::block` / `View::exits` stop at a statement that always exits. Module doc updated. |

Tests: the two `normalize` unit tests are replaced by:

- `early_return_jumps_past_the_callee`: a snapshot of `PKDEC` in kem-dem-cca-blended-parallel.
- `return_under_a_resolved_branch_ends_the_callee`: 4WHS `Send2` in `Hybrid2` (no goto, no dead
  ideal branch) and in `Hybrid3` (a goto and its label).

## 4. Verification

- **Page comparison.** `domino html --no-solver` was run with the binary from before `0db5c7ff`
  and with the final binary, on every example project outside `archive/`. Pages without early
  returns in inlined callees are byte-identical. The four that differ:

  | Page | `goto`s | labels | Where |
  |---|---|---|---|
  | 4WHS `Full4WHS` | 68 | 56 | `PRF.Eval` (44), `MAC.Verify` (24) |
  | 4WHS `Simple4WHS` | 14 | 14 | `Prf.Eval` in games with `bprf: true` |
  | kem-dem-cca-blended-parallel | 4 | 4 | `Scheme_KEMDEM.DEC` |
  | kem-dem-cca-blended-redundant | 4 | 4 | `Scheme_KEMDEM.DEC` |

  Counts cover both the full and the lossy listing. On every page, each goto target has a label.
  `Prf.PRF` appears as often as before (42 times in `Simple4WHS`), so no dead ideal branch is
  printed.
- **Old fallback.** The old pages contain no `// returns from` note. `normalize` handled every
  early return in the examples, so these pages change in how they read, not in what they mean.
  Every remaining goto is a guard (`if … { return }`) whose other path falls through to the rest
  of the callee.
- **Pre-existing failures.** `ae`, `ae-mini`, `nprf` and `rosenpass-basic` fail with the same
  parse or type error on both binaries.
- **Workspace checks.** `cargo test --workspace`: 164 passed, 4 ignored.
  `cargo clippy --workspace --all-targets`: 0 warnings. `cargo fmt --check` is clean.

## 5. Known limitations

1. **Guards read less naturally.** An early return that `normalize` handled with an `else`
   (`MAC.Verify`'s two `return false` guards, `Scheme_KEMDEM.DEC`) is now a goto. This was the
   requested trade: the listing matches the source's shape, at the cost of jumps.
2. **A `for` loop never counts as exiting.** Its body may run zero times, so code after a loop
   whose body returns is always printed. Loops reach the view only when `loopunroll` could not
   unroll them, which has not happened with a returning body in the examples.
3. **Label names are not checked against identifiers.** Labels live in their own namespace
   (`goto L` / `L:`), so a local named `end_P_O` could only confuse a reader. It cannot change
   the meaning.
