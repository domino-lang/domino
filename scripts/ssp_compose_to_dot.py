#!/usr/bin/env python3

"""Generate Graphviz .dot from Domino SSP composition `compose { ... }` graphs.

This focuses on a subset of the grammar relevant for visualizing wiring graphs:
- `composition NAME { ... }`
- `for ... { ... }` blocks (recursed into; loop headers are recorded on edges)
- `compose { SRC: { PORT: DST, ... } ... }`

It is intentionally dependency-free and tolerant of unrelated SSP syntax.

Usage:
  python scripts/ssp_compose_to_dot.py path/to/Game.comp.ssp
  python scripts/ssp_compose_to_dot.py path/to/*.comp.ssp -o out_dir/

    # Also render SVG (requires graphviz 'dot' on PATH)
    python scripts/ssp_compose_to_dot.py path/to/Game.comp.ssp --svg

Then render:
  dot -Tsvg Game.dot > Game.svg
"""

from __future__ import annotations

import argparse
import os
import shutil
import subprocess
from dataclasses import dataclass
from typing import List, Optional, Sequence, Tuple


KW = {
    "composition",
    "compose",
    "instance",
    "for",
    "with",
    "index",
}


@dataclass(frozen=True)
class Token:
    kind: str  # IDENT, KW, SYM, EOF
    value: str
    start: int
    end: int


class Lexer:
    def __init__(self, text: str):
        self.text = text
        self.n = len(text)
        self.i = 0

    def _peek(self, s: str) -> bool:
        return self.text.startswith(s, self.i)

    def _skip_ws_and_comments(self) -> None:
        while self.i < self.n:
            c = self.text[self.i]
            if c in " \t\r\n":
                self.i += 1
                continue
            if self._peek("/*"):
                j = self.text.find("*/", self.i + 2)
                if j == -1:
                    # Unterminated comment; treat remainder as comment.
                    self.i = self.n
                    return
                self.i = j + 2
                continue
            return

    def next_token(self) -> Token:
        self._skip_ws_and_comments()
        if self.i >= self.n:
            return Token("EOF", "", self.n, self.n)

        start = self.i
        c = self.text[self.i]

        if c.isalpha() or c == "_":
            self.i += 1
            while self.i < self.n:
                d = self.text[self.i]
                if d.isalnum() or d == "_":
                    self.i += 1
                else:
                    break
            value = self.text[start:self.i]
            kind = "KW" if value in KW else "IDENT"
            return Token(kind, value, start, self.i)

        # Single-character symbols that matter to our sub-grammar.
        if c in "{}[]():,;":
            self.i += 1
            return Token("SYM", c, start, self.i)

        # Other operators/characters (e.g., '+', '-', '<=', '->', '=')
        # are not needed structurally; return as SYM to allow skipping.
        self.i += 1
        return Token("SYM", c, start, self.i)


@dataclass(frozen=True)
class NodeRef:
    name: str
    suffix: str = ""  # e.g., "[i]" for multi-inst nodes

    def dot_id(self) -> str:
        # Quote everything for safety.
        return dot_quote(self.name + self.suffix)

    def display(self) -> str:
        return self.name + self.suffix


@dataclass(frozen=True)
class Edge:
    src: NodeRef
    dst: NodeRef
    port: str
    modifier: str = ""  # e.g. "with index[...]"
    loop_context: Tuple[str, ...] = ()

    def label(self) -> str:
        base = self.port
        if self.modifier:
            base += f"\\n{self.modifier}"
        if self.loop_context:
            # Keep this compact but informative.
            base += "\\n" + " ; ".join(self.loop_context)
        return base


class ParseError(RuntimeError):
    pass


class Parser:
    def __init__(self, text: str):
        self.text = text
        self.lexer = Lexer(text)
        self.tok = self.lexer.next_token()
        self.edges: List[Edge] = []
        self.compositions: List[str] = []
        self.instance_types: dict[str, str] = {}

    def _advance(self) -> None:
        self.tok = self.lexer.next_token()

    def _accept(
        self, kind: str, value: Optional[str] = None
    ) -> Optional[Token]:
        if self.tok.kind != kind:
            return None
        if value is not None and self.tok.value != value:
            return None
        t = self.tok
        self._advance()
        return t

    def _expect(self, kind: str, value: Optional[str] = None) -> Token:
        t = self._accept(kind, value)
        if t is None:
            want = f"{kind}:{value}" if value is not None else kind
            got = (
                f"{self.tok.kind}:{self.tok.value}"
                if self.tok.kind != "EOF"
                else "EOF"
            )
            raise ParseError(f"Expected {want}, got {got}")
        return t

    def parse(self) -> None:
        while self.tok.kind != "EOF":
            if self.tok.kind == "KW" and self.tok.value == "composition":
                self._parse_composition(loop_ctx=())
            else:
                self._skip_anything()

    def _skip_anything(self) -> None:
        # Skip token or balanced {...} blocks.
        if self._accept("SYM", "{"):
            self._skip_balanced("{")
            return
        self._advance()

    def _skip_balanced(self, opened: str) -> None:
        closing = {"{": "}", "[": "]", "(": ")"}[opened]
        depth = 1
        while self.tok.kind != "EOF" and depth > 0:
            if self._accept("SYM", opened):
                depth += 1
                continue
            if self._accept("SYM", closing):
                depth -= 1
                continue
            self._advance()

    def _parse_composition(self, loop_ctx: Tuple[str, ...]) -> None:
        self._expect("KW", "composition")
        name = self._expect("IDENT").value
        self.compositions.append(name)
        self._expect("SYM", "{")
        self._parse_composition_body(loop_ctx=loop_ctx)
        self._expect("SYM", "}")

    def _parse_composition_body(self, loop_ctx: Tuple[str, ...]) -> None:
        while self.tok.kind != "EOF" and not (
            self.tok.kind == "SYM" and self.tok.value == "}"
        ):
            if self.tok.kind == "KW" and self.tok.value == "compose":
                self._parse_compose(loop_ctx=loop_ctx)
                continue
            if self.tok.kind == "KW" and self.tok.value == "for":
                self._parse_for(loop_ctx=loop_ctx)
                continue
            if (
                self.tok.kind in ("KW", "IDENT")
                and self.tok.value == "instance"
            ):
                self._parse_instance_decl()
                continue
            # Otherwise skip unknown item.
            self._skip_anything()

    def _parse_instance_decl(self) -> None:
        # instance <name> [..]? = <Type> { ... }
        self._expect_any_ident_or_kw()  # 'instance'
        inst_name = self._expect_any_ident_or_kw().value
        if self.tok.kind == "SYM" and self.tok.value == "[":
            # indices_expr; not needed for labeling.
            self._parse_bracketed_raw()

        if not self._accept("SYM", "="):
            return

        type_name = self._expect_any_ident_or_kw().value
        self.instance_types[inst_name] = type_name

        if self._accept("SYM", "{"):
            self._skip_balanced("{")

    def _parse_for(self, loop_ctx: Tuple[str, ...]) -> None:
        # We don't fully parse the header; we keep it as a compact string.
        start = self._expect("KW", "for").start
        # Consume until the opening '{' of the for-body.
        while self.tok.kind != "EOF" and not (
            self.tok.kind == "SYM" and self.tok.value == "{"
        ):
            self._advance()
        brace = self._expect("SYM", "{")
        header = compact_ws(self.text[start:brace.start]).strip()
        new_ctx = loop_ctx + (header,)
        self._parse_composition_body(loop_ctx=new_ctx)
        self._expect("SYM", "}")

    def _parse_compose(self, loop_ctx: Tuple[str, ...]) -> None:
        self._expect("KW", "compose")
        self._expect("SYM", "{")
        while self.tok.kind != "EOF" and not (
            self.tok.kind == "SYM" and self.tok.value == "}"
        ):
            # tolerate stray commas/semicolons
            if self._accept("SYM", ",") or self._accept("SYM", ";"):
                continue
            if self.tok.kind in ("IDENT", "KW"):
                self._parse_compose_assign_body(loop_ctx=loop_ctx)
                continue
            self._advance()
        self._expect("SYM", "}")

    def _parse_compose_assign_body(self, loop_ctx: Tuple[str, ...]) -> None:
        src = self._parse_node_ref_allow_kw()
        self._expect("SYM", ":")
        self._expect("SYM", "{")
        # Zero or more assignments; commas separate; trailing comma allowed.
        while self.tok.kind != "EOF" and not (
            self.tok.kind == "SYM" and self.tok.value == "}"
        ):
            if self._accept("SYM", ","):
                continue
            if self.tok.kind in ("IDENT", "KW"):
                modifier = self._parse_optional_modifier()
                port_tok = self._expect_any_ident_or_kw()
                self._expect("SYM", ":")
                dst = self._parse_node_ref_allow_kw()
                # optional comma
                self._accept("SYM", ",")
                self.edges.append(
                    Edge(
                        src=src,
                        dst=dst,
                        port=port_tok.value,
                        modifier=modifier,
                        loop_context=loop_ctx,
                    )
                )
                continue
            self._advance()
        self._expect("SYM", "}")

    def _expect_any_ident_or_kw(self) -> Token:
        if self.tok.kind not in ("IDENT", "KW"):
            raise ParseError(
                f"Expected identifier, got {self.tok.kind}:{self.tok.value}"
            )
        t = self.tok
        self._advance()
        return t

    def _parse_node_ref_allow_kw(self) -> NodeRef:
        # Some sources are `adversary` which is an identifier, but we also
        # tolerate KW tokens here to be resilient.
        name_tok = self._expect_any_ident_or_kw()
        suffix = ""
        if self.tok.kind == "SYM" and self.tok.value == "[":
            suffix = self._parse_bracketed_raw()
        return NodeRef(name=name_tok.value, suffix=suffix)

    def _parse_optional_modifier(self) -> str:
        if not (self.tok.kind == "KW" and self.tok.value == "with"):
            return ""
        with_tok = self._expect("KW", "with")
        if not (self.tok.kind == "KW" and self.tok.value == "index"):
            # Unknown modifier; include the keyword only.
            return "with"
        self._expect("KW", "index")
        if not (self.tok.kind == "SYM" and self.tok.value == "["):
            return "with index"
        bracket = self._parse_bracketed_raw()
        raw = compact_ws(self.text[with_tok.start:self.lexer.i]).strip()
        # raw likely includes trailing whitespace; normalize for labels
        if bracket:
            return f"with index {compact_ws(bracket)}"
        return compact_ws(raw)

    def _parse_bracketed_raw(self) -> str:
        # Returns the original slice for bracketed expr, e.g. "[i, j+1]".
        open_tok = self._expect("SYM", "[")
        depth = 1
        last_end = open_tok.end
        while self.tok.kind != "EOF" and depth > 0:
            if self.tok.kind == "SYM" and self.tok.value == "[":
                depth += 1
                last_end = self.tok.end
                self._advance()
                continue
            if self.tok.kind == "SYM" and self.tok.value == "]":
                depth -= 1
                last_end = self.tok.end
                self._advance()
                if depth == 0:
                    break
                continue
            last_end = self.tok.end
            self._advance()
        return self.text[open_tok.start:last_end]


def compact_ws(s: str) -> str:
    return " ".join(s.split())


def dot_quote(s: str) -> str:
    s = s.replace("\\", "\\\\").replace('"', '\\"')
    return f'"{s}"'


def infer_output_path(input_path: str, out: Optional[str], ext: str) -> str:
    base = os.path.splitext(os.path.basename(input_path))[0]
    filename = base + ext
    if out is None:
        return os.path.join(os.path.dirname(input_path), filename)
    if out.endswith(os.sep) or (os.path.exists(out) and os.path.isdir(out)):
        return os.path.join(out, filename)
    # With multiple inputs, caller should pass a directory.
    return out


def collapse_parallel_edges(
    edges: Sequence[Edge], label_sep: str = ", "
) -> List[Tuple[NodeRef, NodeRef, str]]:
    """Collapse parallel edges (same src,dst) into one with combined label."""

    grouped: dict[Tuple[str, str], Tuple[NodeRef, NodeRef, List[str]]] = {}
    for e in edges:
        key = (e.src.display(), e.dst.display())
        label = e.label()
        if key not in grouped:
            grouped[key] = (e.src, e.dst, [label])
        else:
            labels = grouped[key][2]
            if label not in labels:
                labels.append(label)

    collapsed: List[Tuple[NodeRef, NodeRef, str]] = []
    for _key, (src, dst, labels) in grouped.items():
        combined = label_sep.join(labels)
        collapsed.append((src, dst, combined))
    return collapsed


def node_label(
    node: NodeRef,
    instance_types: dict[str, str],
    mode: str,
) -> str:
    if node.display() == "adversary":
        return "adversary"
    if mode == "type":
        t = instance_types.get(node.name)
        if t is not None:
            return t + node.suffix
    return node.display()


def to_dot(
    graph_name: str,
    edges: Sequence[Edge],
    instance_types: Optional[dict[str, str]] = None,
    rankdir: str = "LR",
    collapse_parallel: bool = True,
    parallel_label_sep: str = ", ",
    node_labels: str = "instance",
) -> str:
    if instance_types is None:
        instance_types = {}
    nodes = {}
    for e in edges:
        nodes[e.src.display()] = e.src
        nodes[e.dst.display()] = e.dst

    lines: List[str] = []
    lines.append(f"digraph {dot_quote(graph_name)} {{")
    lines.append(f"  rankdir={rankdir};")
    lines.append("  splines=true;")
    lines.append("  concentrate=false;")
    lines.append("  node [shape=box, fontname=\"Helvetica\"];\n")

    # Style special nodes if present.
    if "adversary" in nodes:
        lines.append(
            '  "adversary" [shape=oval, style=filled, fillcolor="#e6e6e6"];'
        )

    # Emit all other nodes explicitly for stable output.
    for key in sorted(nodes.keys()):
        if key == "adversary":
            continue
        lbl = node_label(nodes[key], instance_types, node_labels)
        lines.append(
            f"  {nodes[key].dot_id()} [label={dot_quote(lbl)}];"
        )

    lines.append("")

    if collapse_parallel:
        out_edges = collapse_parallel_edges(
            edges,
            label_sep=parallel_label_sep,
        )
        for src, dst, label in out_edges:
            lines.append(
                f"  {src.dot_id()} -> {dst.dot_id()} "
                f"[label={dot_quote(label)}];"
            )
    else:
        for e in edges:
            label = e.label()
            lines.append(
                f"  {e.src.dot_id()} -> {e.dst.dot_id()} "
                f"[label={dot_quote(label)}];"
            )

    lines.append("}")
    return "\n".join(lines) + "\n"


def parse_file(path: str) -> Tuple[str, List[Edge], dict[str, str]]:
    with open(path, "r", encoding="utf-8") as f:
        text = f.read()

    p = Parser(text)
    p.parse()

    # If there are multiple compositions, choose the first name.
    name = p.compositions[0] if p.compositions else os.path.basename(path)
    return name, p.edges, p.instance_types


def render_dot_to_svg(dot: str, svg_path: str) -> None:
    if shutil.which("dot") is None:
        raise RuntimeError(
            "Graphviz 'dot' not found on PATH. Install graphviz "
            "or run without --svg."
        )
    proc = subprocess.run(
        ["dot", "-Tsvg"],
        input=dot.encode("utf-8"),
        stdout=subprocess.PIPE,
        stderr=subprocess.PIPE,
        check=False,
    )
    if proc.returncode != 0:
        raise RuntimeError(
            "dot failed:\n" + proc.stderr.decode("utf-8", errors="replace")
        )
    with open(svg_path, "wb") as f:
        f.write(proc.stdout)


def main(argv: Optional[Sequence[str]] = None) -> int:
    ap = argparse.ArgumentParser(
        description="Generate Graphviz .dot from SSP compose graphs"
    )
    ap.add_argument(
        "inputs",
        nargs="+",
        help=".comp.ssp (or any SSP) files to parse",
    )
    ap.add_argument(
        "-o",
        "--out",
        default=None,
        help="Output file (single input) or output directory (multi input)",
    )
    ap.add_argument(
        "--rankdir",
        default="LR",
        choices=["LR", "TB", "RL", "BT"],
        help="Graphviz rankdir",
    )
    ap.add_argument(
        "--collapse-parallel",
        action=argparse.BooleanOptionalAction,
        default=True,
        help="Collapse parallel edges (same src,dst) into one combined label",
    )
    ap.add_argument(
        "--node-labels",
        choices=["instance", "type"],
        default="instance",
        help="Label nodes by instance name or by package type",
    )
    ap.add_argument(
        "--parallel-label-sep",
        default=", ",
        help=(
            "Separator used when combining labels for collapsed parallel edges"
        ),
    )
    ap.add_argument(
        "--svg",
        action="store_true",
        help="Also render an .svg next to the .dot (requires graphviz 'dot')",
    )
    ap.add_argument(
        "--svg-only",
        action="store_true",
        help="Only write .svg output (implies --svg)",
    )
    args = ap.parse_args(argv)

    if len(args.inputs) > 1 and args.out is not None and not (
        args.out.endswith(os.sep)
        or (os.path.exists(args.out) and os.path.isdir(args.out))
    ):
        ap.error(
            "When passing multiple inputs, --out must be a directory path "
            "ending with '/' or an existing directory"
        )

    if args.out is not None and (
        args.out.endswith(os.sep) and not os.path.exists(args.out)
    ):
        os.makedirs(args.out, exist_ok=True)

    if args.svg_only:
        args.svg = True

    for inp in args.inputs:
        name, edges, instance_types = parse_file(inp)
        dot = to_dot(
            name,
            edges,
            instance_types=instance_types,
            rankdir=args.rankdir,
            collapse_parallel=args.collapse_parallel,
            parallel_label_sep=args.parallel_label_sep,
            node_labels=args.node_labels,
        )

        dot_path = infer_output_path(inp, args.out, ".dot")
        svg_path = infer_output_path(inp, args.out, ".svg")

        if not args.svg_only:
            with open(dot_path, "w", encoding="utf-8") as f:
                f.write(dot)
            print(dot_path)

        if args.svg:
            render_dot_to_svg(dot, svg_path)
            print(svg_path)

    return 0


if __name__ == "__main__":
    raise SystemExit(main())
