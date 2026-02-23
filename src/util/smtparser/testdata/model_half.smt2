(
; cardinality of Bits_n is 1
; rep: (as @Bits_n_0 Bits_n)
(define-fun __sample-rand-medium_composition-Bits_n ((_arg_1 SampleId) (_arg_2 Int)) Bits_n (as @Bits_n_0 Bits_n))
(define-fun __sample-rand-small_composition-Bits_n ((_arg_1 SampleId) (_arg_2 Int)) Bits_n (as @Bits_n_0 Bits_n))
(define-fun <<game-state-medium_composition-old>> () <GameState_MediumComposition_<$<!n!>$>> (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> 1) (<mk-pkg-state-Fwd-<$<!n!>$>> 0) 0 (- 1)))
(define-fun <<game-state-small_composition-old>> () <GameState_SmallComposition_<$<!n!>$>> (<mk-game-SmallComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> 0) 0 2))
(define-fun <<theorem-consts>> () <TheoremConsts_Proof> (<mk-theorem-consts-Proof> 0))
(define-fun <return-medium_composition-UsefulOracle> () <OracleReturn_MediumComposition_<$<!n!>$>_Fwd_<$<!n!>$>_UsefulOracle> (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle> (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> 2) (<mk-pkg-state-Fwd-<$<!n!>$>> 0) 1 (- 1)) ((as mk-return-value (ReturnValue (Tuple2 Int Bits_n))) ((as mk-tuple2 (Tuple2 Int Bits_n)) 2 (as @Bits_n_0 Bits_n)))))
(define-fun return-value-medium_composition-fwd-UsefulOracle () (ReturnValue (Tuple2 Int Bits_n)) ((as mk-return-value (ReturnValue (Tuple2 Int Bits_n))) ((as mk-tuple2 (Tuple2 Int Bits_n)) 2 (as @Bits_n_0 Bits_n))))
(define-fun <return-is-abort-medium_composition-fwd-UsefulOracle> () Bool false)
(define-fun <<game-state-me
