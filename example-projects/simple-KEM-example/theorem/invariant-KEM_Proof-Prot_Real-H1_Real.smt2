; left: Prot, right: H1 (Corr_KEM + Corr_reduction)
(define-state-relation invariant
  (left right)
  (and
    (= left.Prot.SENTCTXT     right.Corr_reduction.SENTCTXT)
    (= left.Prot.SENTKEY      right.Corr_reduction.SENTKEY)
    (= left.Prot.RECEIVEDCTXT right.Corr_reduction.RECEIVEDCTXT)
    (= left.Prot.RECEIVEDKEY  right.Corr_reduction.RECEIVEDKEY)
    (= left.Prot.TESTED       right.Corr_reduction.TESTED)
    (= left.Prot.ctr          right.Corr_reduction.ctr)
    (= left.Prot.sk           right.Corr_KEM.sk)
    (= left.Prot.pk           right.Corr_KEM.pk)))

; Each sample operation is fully indexec by the pair (statement id, sample counter)
; "stmt" – Each instructions containing a sampling operation in the game is assigned a statement id number; check the generated latex code for the proof (not games/compositions or packages) to find the statement ids.
; "offset" – Each sample operation also has a counter
;
; These indices are given for both games; the game on the left and the game on the right.
(define-fun randomness-mapping-GetPK (
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (offset-left Int)
  (offset-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "GetPK" "secret_key"))
    (= stmt-right (sample-id "Corr_KEM" "GetPK" "secret_key"))
    (= offset-left offset-right)
  )
)

(define-fun randomness-mapping-Run (
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (offset-left Int)
  (offset-right Int)
) Bool
; BEGIN FUNCTION BODY
  (or 
    (and
      (= stmt-left (sample-id "Prot" "Run" "secret_key"))
      (= stmt-right (sample-id "Corr_KEM" "ENC_and_DEC" "secret_key"))
      (= offset-left offset-right)
    )
    (and
      (= stmt-left (sample-id "Prot" "Run" "encaps_rand"))
      (= stmt-right (sample-id "Corr_KEM" "ENC_and_DEC" "encaps_rand"))
      (= offset-left offset-right)
    )
  )
)

(define-fun randomness-mapping-TestSender (
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (offset-left Int)
  (offset-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "TestSender" "encapsulated_key"))
    (= stmt-right (sample-id "Corr_reduction" "TestSender" "encapsulated_key"))
    (= offset-left offset-right)
  )
)

(define-fun randomness-mapping-TestReceiver (
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (offset-left Int)
  (offset-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "TestReceiver" "encapsulated_key"))
    (= stmt-right (sample-id "Corr_reduction" "TestReceiver" "encapsulated_key"))
    (= offset-left offset-right)
  )
)
