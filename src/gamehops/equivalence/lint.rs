use super::error::Result;
use super::EquivalenceContext;
use crate::transforms::samplify::Position as SamplePosition;
use crate::util::smtparser::ExtractedFunction;
use crate::writers::smt::contexts::GameInstanceContext;
use crate::writers::smt::patterns::datastructures::DatastructurePattern;

pub(super) struct Linter<'a> {
    context: &'a EquivalenceContext<'a>,
    oracle_name: &'a str,
    left_sample_pos: &'a Vec<SamplePosition>,
    right_sample_pos: &'a Vec<SamplePosition>,
    functions: Vec<ExtractedFunction>,
}

impl<'a> Linter<'a> {
    pub(super) fn new(context: &'a EquivalenceContext<'a>, oracle_name: &'a str) -> Self {
        let left_sample_pos = &context.sample_info_left().positions;
        let right_sample_pos = &context.sample_info_right().positions;

        Linter {
            context,
            oracle_name,
            left_sample_pos,
            right_sample_pos,
            functions: Vec::new(),
        }
    }

    pub(super) fn lint_file(&mut self, filename: &str, content: &str) -> Result<()> {
        let parsed_sampleids = crate::util::smtparser::extract_sampleid(&content);
        self.functions
            .append(&mut crate::util::smtparser::extract_functions(&content));

        for sampleinfo in &parsed_sampleids {
            if !self.left_sample_pos.iter().any(|samplepos| {
                samplepos.inst_name == sampleinfo.pkgname
                    && samplepos.oracle_name == sampleinfo.oraclename
                    && samplepos.sample_name == sampleinfo.samplename
            }) && !self.right_sample_pos.iter().any(|samplepos| {
                samplepos.inst_name == sampleinfo.pkgname
                    && samplepos.oracle_name == sampleinfo.oraclename
                    && samplepos.sample_name == sampleinfo.samplename
            }) {
                let smtfun = &sampleinfo.smtfunname;
                log::warn!("Smt code in {filename} uses {sampleinfo} in function {smtfun} which does not occur in package code");
            }
        }
        Ok(())
    }

    pub(super) fn lint_finish(&self) -> Result<()> {
        let left_game_ctx = self.context.left_game_inst_ctx();
        let right_game_ctx = self.context.right_game_inst_ctx();

        if let Some(fun) = self
            .functions
            .iter()
            .find(|fun| fun.smtfunname == "invariant")
        {
            if fun.smtargs.len() != 2 {
                log::warn!("\"invariant\" function takes exactly two arguments");
            } else {
                let left_expected_sort =
                    left_game_ctx.datastructure_game_state_pattern().sort_name();
                let right_expected_sort = right_game_ctx
                    .datastructure_game_state_pattern()
                    .sort_name();
                if fun.smtargs[1].1 != left_expected_sort {
                    log::warn!("left argument of \"invariant\" should be of sort {left_expected_sort}, not {}", fun.smtargs[1].1)
                }
                if fun.smtargs[1].1 != right_expected_sort {
                    log::warn!("right argument of \"invariant\" should be of sort {right_expected_sort}, not {}", fun.smtargs[1].1)
                }
            }
        } else {
            log::warn!("None of the smt files declares an function called \"invariant\"");
        }

        let randomness_fun_name = format!("randomness-mapping-{}", self.oracle_name);
        if let Some(fun) = self
            .functions
            .iter()
            .find(|fun| fun.smtfunname == randomness_fun_name)
        {
            if fun.smtargs.len() != 6 {
                log::warn!("\"{randomness_fun_name}\" function takes exactly two arguments");
            } else {
                if !fun
                    .smtargs
                    .iter()
                    .zip(&["Int", "Int", "SampleId", "SampleId", "Int", "Int"])
                    .all(|((_argname, argtype), expectedtype)| argtype == expectedtype)
                {
                    log::warn!("\"{randomness_fun_name}\" function has wrong argument sorts, should be (Int Int SampleId SampleId Int Int)");
                }
            }
        } else {
            log::warn!(
                "None of the smt files declares a randomness mapping for oracle \"{}\"",
                self.oracle_name
            );
        }

        Ok(())
    }
}
