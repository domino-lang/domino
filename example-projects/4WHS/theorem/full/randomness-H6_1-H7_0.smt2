(define-fun randomness-mapping-NewSession
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)

(define-fun randomness-mapping-NewKey
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send1
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send2 
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (or (= id-0 id-1 (sample-id "Nonces" "Sample" "1"))
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
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (and (= id-0 (sample-id "PRF" "Eval" "1"))
        (= id-1 (sample-id "MAC" "Init" "1")))))

(define-fun randomness-mapping-Send4
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)

(define-fun randomness-mapping-Send5
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)

(define-fun randomness-mapping-Reveal
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 id-1)))

(define-fun randomness-mapping-Test
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and (= base-ctr-0 scr-0)
       (= base-ctr-1 scr-1)
       (= id-0 id-1)))

(define-fun randomness-mapping-SameKey
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)

(define-fun randomness-mapping-AtMost
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)

(define-fun randomness-mapping-AtLeast
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  false)
