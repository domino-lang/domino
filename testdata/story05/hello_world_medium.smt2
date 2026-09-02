; decls
(declare-const <v!left!0!ctr>
               Int)

(declare-const <v!left!1!ctr>
               Int)

(declare-const <v!left!2!ctr>
               Int)

(declare-const <v!left!3!rand>
               Bits_n)

(declare-const <v!left!4!y>
               (Tuple2 Int
                       Bits_n))

(declare-const <v!left!5!gamestate>
               <GameState_MediumComposition_<$<!n!>$>>)

(declare-const <v!left!6!gamestate>
               <GameState_MediumComposition_<$<!n!>$>>)

(declare-const <v!left!7!gamestate>
               <GameState_MediumComposition_<$<!n!>$>>)

; constraints
(assert (= <v!left!0!ctr>
           (<pkg-state-Rand-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <<game-state-medium_composition-old>>))))

(assert (= <v!left!1!ctr>
           (<pkg-state-Fwd-<$<!n!>$>-ctr> (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <<game-state-medium_composition-old>>))))

(assert (= <v!left!2!ctr>
           (+ <v!left!0!ctr>
              1)))

(assert (= <v!left!3!rand>
           (__sample-rand-medium_composition-Bits_n (sample-id "rand"
                                                               "UsefulOracle"
                                                               "samplepoint")
                                                    0)))

(assert (= <v!left!4!y>
           (mk-tuple2 <v!left!2!ctr>
                      <v!left!3!rand>)))

(assert (= <v!left!5!gamestate>
           (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <<game-state-medium_composition-old>>)
                                                  (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <<game-state-medium_composition-old>>)
                                                  (+ 1
                                                     (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <<game-state-medium_composition-old>>))
                                                  (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <<game-state-medium_composition-old>>))))

(assert (= <v!left!6!gamestate>
           (<mk-game-MediumComposition-<$<!n!>$>> (<mk-pkg-state-Rand-<$<!n!>$>> <v!left!2!ctr>)
                                                  (<game-MediumComposition-<$<!n!>$>-pkgstate-fwd> <v!left!5!gamestate>)
                                                  (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <v!left!5!gamestate>)
                                                  (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <v!left!5!gamestate>))))

(assert (= <v!left!7!gamestate>
           (<mk-game-MediumComposition-<$<!n!>$>> (<game-MediumComposition-<$<!n!>$>-pkgstate-rand> <v!left!6!gamestate>)
                                                  (<mk-pkg-state-Fwd-<$<!n!>$>> <v!left!1!ctr>)
                                                  (<game-MediumComposition-<$<!n!>$>-rand-rand-UsefulOracle-samplepoint> <v!left!6!gamestate>)
                                                  (<game-MediumComposition-<$<!n!>$>-rand-rand-UselessOracle-1> <v!left!6!gamestate>))))

; return
(assert (= <return-medium_composition-UsefulOracle>
           (<mk-oracle-return-MediumComposition-<$<!n!>$>-Fwd-<$<!n!>$>-UsefulOracle> <v!left!7!gamestate>
                                                                                      (mk-return-value <v!left!4!y>))))

