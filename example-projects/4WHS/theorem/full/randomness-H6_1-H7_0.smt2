(define-fun randomness-mapping-Send2 
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 0)
   (= offset-1 0)
   (or (and (= id-0 (sample-id "Nonces" "Sample" "1"))
            (= id-1 (sample-id "Nonces" "Sample" "1")))
       (and (= id-0 (sample-id "PRF" "Eval" "1"))
            (= id-1 (sample-id "MAC" "Init" "1"))))))


; rand-PRF-Eval-1
(define-fun <relation-lemma-randomness-H6_1_1-H7_0-Send2>
    ((H61-old <GameState_H6_<$<!n!>$>>)
     (H70-old <GameState_H7_<$<!n!>$>>)
     (H61-return <OracleReturn_H6_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Send2>)
     (H70-return <OracleReturn_H7_<$<!n!>$>_KX_noprfkey_<$<!n!>$>_Send2>)
     (ctr Int) (msg Bits_n))
  Bool
  (and (= (__sample-rand-H6_1_1-Bits_n (sample-id "Nonces" "Sample" "1")
                                       (<game-H6-<$<!n!>$>-rand-Nonces-Sample-1> H61-old))
          (__sample-rand-H7_0-Bits_n (sample-id "Nonces" "Sample" "1")
                                       (<game-H7-<$<!n!>$>-rand-Nonces-Sample-1> H70-old)))
       (= (__sample-rand-H6_1_1-Bits_n (sample-id "PRF" "Eval" "1")
                                       (<game-H6-<$<!n!>$>-rand-PRF-Eval-1> H61-old))
          (__sample-rand-H7_0-Bits_n (sample-id "MAC" "Init" "1")
                                       (<game-H7-<$<!n!>$>-rand-MAC-Init-1> H70-old)))))

(define-fun randomness-mapping-Send3
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 0)
   (= offset-1 0)
   (and (= id-0 (sample-id "PRF" "Eval" "1"))
        (= id-1 (sample-id "MAC" "Init" "1")))))
