(define-fun randomness-mapping-NewSession
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)

(define-fun randomness-mapping-NewKey
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send1
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send2
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send3
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 id-1)))

(define-fun randomness-mapping-Send4
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)

(define-fun randomness-mapping-Send5
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)

(define-fun randomness-mapping-Test
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and
   (= offset-0 0)
   (= offset-1 0)
   (= id-0 (sample-id "PRF" "Eval" "1"))
   (= id-1 (sample-id "KX" "Test" "1"))))

(define-fun randomness-mapping-Reveal
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  (and (= offset-0 0)
       (= offset-1 0)
       (= id-0 id-1)))

(define-fun randomness-mapping-SameKey
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)

(define-fun randomness-mapping-AtMost
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)

(define-fun randomness-mapping-AtLeast
    ((id-0 SampleId) (id-1 SampleId)
     (offset-0 Int) (offset-1 Int))
  Bool
  false)
