// SPDX-License-Identifier: MIT OR Apache-2.0

//! Generates a representative lemma-dependency HTML page from hand-built
//! sample data (not a real project) so the exporter can be exercised and
//! visually/behaviorally checked (e.g. via a headless browser) without
//! needing a full Domino project on hand.
//!
//! The claim trees are hand-built `Claim`s, but the per-claim sources are
//! run through the real [`sspverif::writers::claim_source::collect_claim_sources`]
//! parser (same as production) so this also exercises the real
//! Domino-macro-capture and SMT-to-EasyCrypt translation pipeline end to
//! end, not just hand-typed expectations.
//!
//! The SMT text below deliberately follows Domino's real naming convention
//! for the two claim-name lookup cases (see
//! `sspverif::writers::html::claim_smt_lookup_key`): `relation-*`/`invariant-*`
//! claims are asserted under their bare name, while every other claim name
//! (the common case -- an ordinary lemma) gets mangled by Domino's own
//! `FunctionNameBuilder` into `<relation-{name}-{left}-{right}-{oracle}>`.
//!
//! Usage: `cargo run --example html_export_demo -- <output-path>`

use std::env;

use sspverif::theorem::Claim;
use sspverif::writers::claim_source::collect_claim_sources;
use sspverif::writers::html::lemma_dependency_html;

const LEFT_NAME: &str = "Game_Real";
const RIGHT_NAME: &str = "Game_Ideal";

fn claim(name: &str, deps: &[&str], admitted: bool) -> Claim {
    Claim::from_tuple((
        name.to_string(),
        deps.iter().map(|d| d.to_string()).collect(),
        admitted,
        true,
        None,
    ))
}

const ENC_INVARIANTS: &str = r#"
(define-state-relation relation-invariant-Enc
    (left-game right-game)
    (= left-game.KEM.sk right-game.KEM.sk))

(define-lemma relation-lemma-ciphertexts-match-Enc
    (old-state-left old-state-right return-left return-right (m Bits_n))
    (= return-left.value return-right.value))

(define-lemma <relation-lemma-key-agreement-Game_Real-Game_Ideal-Enc>
    (old-state-left old-state-right return-left return-right)
    (kem-correctness old-state-right.KEM.pk old-state-right.KEM.sk))

(define-fun kem-correctness
    ((pk (Maybe Bits_pkeyl)) (sk (Maybe Bits_skeyl)))
    Bool
    (=> (pk-valid pk) (= pk pk)))

(define-fun pk-valid
    ((pk (Maybe Bits_pkeyl)))
    Bool
    (not (is-mk-none pk)))
"#;
// lemma-admitted-example is admitted in the theorem's `lemmas {}` block (see
// `enc_tree` below), so -- like a real admitted claim -- it deliberately has
// no `define-lemma` body here: nothing needs proving, so nothing needs
// defining. The exporter should fall back to "source not captured" for it.

const DEC_INVARIANTS: &str = r#"
(define-lemma relation-lemma-plaintexts-match-Dec
    (old-state-left old-state-right return-left return-right (c Bits_n))
    (and
        (= return-left.value return-right.value)
        (=> (is-mk-some return-left.value)
            (= (maybe-get return-left.value) (maybe-get return-right.value)))))
"#;

fn main() {
    let out_path = env::args()
        .nth(1)
        .unwrap_or_else(|| "demo.html".to_string());

    let enc_tree = vec![
        claim("equal-aborts", &[], false),
        claim("no-abort", &[], false),
        claim(
            "same-output",
            &["relation-lemma-ciphertexts-match-Enc"],
            false,
        ),
        claim(
            "invariant",
            &[
                "relation-invariant-Enc",
                "no-abort",
                "lemma-admitted-example",
            ],
            false,
        ),
        claim("relation-invariant-Enc", &[], false),
        claim(
            "relation-lemma-ciphertexts-match-Enc",
            &["lemma-key-agreement"],
            false,
        ),
        claim("lemma-key-agreement", &[], false),
        claim("lemma-admitted-example", &[], true),
    ];

    let dec_tree = vec![
        claim("equal-aborts", &[], false),
        claim(
            "same-output",
            &["relation-lemma-plaintexts-match-Dec"],
            false,
        ),
        claim("invariant", &["no-abort"], false),
        claim("relation-lemma-plaintexts-match-Dec", &[], false),
    ];

    let trees = vec![("Enc".to_string(), enc_tree), ("Dec".to_string(), dec_tree)];
    let claim_sources = vec![
        ("Enc".to_string(), collect_claim_sources(ENC_INVARIANTS)),
        ("Dec".to_string(), collect_claim_sources(DEC_INVARIANTS)),
    ];

    let html = lemma_dependency_html(
        "Real_Ideal",
        "MyTheorem: Game_Real == Game_Ideal",
        LEFT_NAME,
        RIGHT_NAME,
        &trees,
        &claim_sources,
    );

    std::fs::write(&out_path, html).expect("failed to write output HTML");
    eprintln!("wrote {out_path}");
}
