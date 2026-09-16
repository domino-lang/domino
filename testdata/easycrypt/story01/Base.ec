(* Fixture theory for kitchen-sink.ec's `EcItem::Clone` case. Every .ec file
   is implicitly a theory named after the file, so this gives `clone` a base
   theory to specialise without needing a `theory ... end` item variant,
   which is out of scope for story 01 (`ast.rs` models no such item). *)
type t.
op dummy : int.
