(define-fun <relation-always-aborts-H7_1_1_0-H7_1_1_1-Test>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Test>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Test>)
     (ctr Int))
  Bool
  (is-mk-abort (<oracle-return-H7-<$<!n!>$>-KX_noprfkey-<$<!n!>$>-Test-return-value-or-abort> H710-return)))

(define-fun <relation-always-aborts-H7_1_1_0-H7_1_1_1-Reveal>
    ((H710-old <GameState_H7_<$<!n!>$>>)
     (H711-old <GameState_H7_<$<!n!>$>>)
     (H710-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Reveal>)
     (H711-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Reveal>)
     (ctr Int))
  Bool
  (is-mk-abort (<oracle-return-H7-<$<!n!>$>-KX_noprfkey-<$<!n!>$>-Reveal-return-value-or-abort> H710-return)))
