use crate::ui::TheoremUI;
use mockall::mock;

mock! {
    pub(crate) TestTheoremUI {}

    impl TheoremUI for TestTheoremUI {

        fn println(&self, line: &str) -> std::io::Result<()>;

        fn start_theorem(&mut self, theorem_name: &str, num_theoremsteps: u64);

        fn finish_theorem(&mut self, theorem_name: &str);

        fn start_theoremstep(&mut self, theorem_name: &str, theoremstep_name: &str);

        fn theoremstep_is_reduction(&mut self, theorem_name: &str, theoremstep_name: &str);

        fn theoremstep_set_oracles(&mut self, theorem_name: &str, theoremstep_name: &str, num_oracles: u64);

        fn finish_theoremstep(&mut self, theorem_name: &str, theoremstep_name: &str);

        fn start_oracle(
            &mut self,
            theorem_name: &str,
            theoremstep_name: &str,
            oracle_name: &str,
            num_lemmata: u64,
        );

        fn finish_oracle(&mut self, theorem_name: &str, theoremstep_name: &str, oracle_name: &str);

        fn start_lemma(
            &mut self,
            theorem_name: &str,
            theoremstep_name: &str,
            oracle_name: &str,
            lemma_name: &str,
        );

        fn finish_lemma(
            &mut self,
            theorem_name: &str,
            theoremstep_name: &str,
            oracle_name: &str,
            lemma_name: &str,
        );
    }
}
