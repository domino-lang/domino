# domino-ast

This project contains the type definition and parsing code for the AST
of Domino. Actually, it might technically be a CST, but who is counting.

We are using a mix of techniques here in order to achieve relatively
high correctness promises from the type system, references to AST nodes
without lifetimes, and compact IDs for AST nodes that we can use to
refer to them in side tables.

The general idea is that we have per-type custom arenas, which are plain
`Vec`s. We have types `Ref` and `Slice` which hold the offset in the
vector, and for `Slice` also the length of the run. These offsets are
also used as keys in side tables.

This way, during resolution we can create a side table as a
`Vec<Option<V>>` of the same size as the number of nodes. After the
resolution pass we can iterate over the table and check that there are no
`None`, and convert to `Vec<V>`.

For source locations, we don't want per-node tables, because we need
it for everything, and that would mean a lot of side tables. Instead,
we define a global id type that is an enum with variants for each node
type. We then use that as the key in a plain HashMap.
