(define-fun randomness-mapping
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (and
   (= scr-1 base-ctr-1)
   (= scr-0 base-ctr-0)
   (= id-0 id-1)))



(define-fun randomness-mapping-NewKey
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-NewSession
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Send1
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Send2
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Send3
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Send4
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Send5
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Test
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
(define-fun randomness-mapping-Reveal
    ((base-ctr-0 Int) (base-ctr-1 Int)
     (id-0 SampleId) (id-1 SampleId)
     (scr-0 Int) (scr-1 Int))
  Bool
  (randomness-mapping base-ctr-0 base-ctr-1
                      id-0 id-1
                      scr-0 scr-1))
