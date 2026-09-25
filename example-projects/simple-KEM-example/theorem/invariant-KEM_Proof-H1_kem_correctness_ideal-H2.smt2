; left: H1 (Corr_KEM + Corr_reduction), right: H2 (CPA + H2_CPA_reduction)
(define-state-relation invariant
  (left right)
  (and
    (= left.Corr_reduction.SENTCTXT     left.Corr_reduction.RECEIVEDCTXT)
    (= left.Corr_reduction.SENTKEY      left.Corr_reduction.RECEIVEDKEY)
    (= left.Corr_reduction.SENTCTXT     right.CPA.CTXT)
    (= left.Corr_reduction.SENTKEY      right.CPA.KEY)
    (= left.Corr_reduction.RECEIVEDCTXT right.CPA.CTXT)
    (= left.Corr_reduction.RECEIVEDKEY  right.CPA.KEY)
    (= left.Corr_reduction.TESTED       right.CPA.TESTED)
    (= left.Corr_reduction.ctr          right.CPA.ctr)
    (= left.Corr_KEM.sk                 right.CPA.sk)
    (= left.Corr_KEM.pk                 right.CPA.pk)))

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
    (= stmt-left (sample-id "Corr_KEM" "GetPK" "secret_key"))
    (= stmt-right (sample-id "CPA" "GetPK" "secret_key"))
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
      (= stmt-left (sample-id "Corr_KEM" "ENC_and_DEC" "secret_key"))
      (= stmt-right (sample-id "CPA" "ENC" "secret_key"))
      (= offset-left offset-right)
    )
    (and
      (= stmt-left (sample-id "Corr_KEM" "ENC_and_DEC" "encaps_rand"))
      (= stmt-right (sample-id "CPA" "ENC" "encaps_rand"))
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
    (= stmt-left (sample-id "Corr_reduction" "TestSender" "encapsulated_key"))
    (= stmt-right (sample-id "CPA" "Test" "encapsulated_key"))
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
    (= stmt-left (sample-id "Corr_reduction" "TestReceiver" "encapsulated_key"))
    (= stmt-right (sample-id "CPA" "Test" "encapsulated_key"))
    (= offset-left offset-right)
  )
)
