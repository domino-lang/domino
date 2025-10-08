(define-fun invariant ( 
  (prot    <GameState_Prot>)
  (h1      <GameState_H1>)
) Bool
; BEGIN FUNCTION BODY
  (let 
    (
      (prot.prot   (<game-Prot-pkgstate-Prot>   prot    ))
      (h1.corr_kem (<game-H1-pkgstate-Corr_KEM> h1      ))
      (h1.corr_red (<game-H1-pkgstate-Corr_reduction> h1))
    )
    ; BEGIN LET DEFINITION USAGE
    (and 
      (= (<pkg-state-Prot-SENTCTXT>           prot.prot)
         (<pkg-state-Corr_reduction-SENTCTXT> h1.corr_red))
      (= (<pkg-state-Prot-SENTKEY>            prot.prot)
         (<pkg-state-Corr_reduction-SENTKEY>  h1.corr_red))
      (= (<pkg-state-Prot-RECEIVEDCTXT>       prot.prot)
         (<pkg-state-Corr_reduction-RECEIVEDCTXT> h1.corr_red))
      (= (<pkg-state-Prot-RECEIVEDKEY>        prot.prot)
         (<pkg-state-Corr_reduction-RECEIVEDKEY> h1.corr_red))
      (= (<pkg-state-Prot-TESTED>             prot.prot)
         (<pkg-state-Corr_reduction-TESTED>   h1.corr_red))
      (= (<pkg-state-Prot-ctr>                prot.prot)
         (<pkg-state-Corr_reduction-ctr>      h1.corr_red))
      (= (<pkg-state-Prot-sk>                 prot.prot)
         (<pkg-state-Corr_KEM-sk>             h1.corr_kem))
      (= (<pkg-state-Prot-pk>                 prot.prot)
         (<pkg-state-Corr_KEM-pk>             h1.corr_kem))
    )
  )
)

; Each sample operation is fully indexec by the pair (statement id, sample counter)
; "stmt" – Each instructions containing a sampling operation in the game is assigned a statement id number; check the generated latex code for the proof (not games/compositions or packages) to find the statement ids.
; "ctr" – Each sample operation also has a counter
; "base-ctr" – Additionally, we are given a zero-counter; this is useful if we want to compute offsets
;
; These indices are given for both games; the game on the left and the game on the right.
(define-fun randomness-mapping-GetPK (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "GetPK" "secret_key"))
    (= stmt-right (sample-id "Corr_KEM" "GetPK" "secret_key"))
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)

(define-fun randomness-mapping-Run (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (or 
    (and
      (= stmt-left (sample-id "Prot" "Run" "secret_key"))
      (= stmt-right (sample-id "Corr_KEM" "ENC_and_DEC" "secret_key"))
      (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
    )
    (and
      (= stmt-left (sample-id "Prot" "Run" "encaps_rand"))
      (= stmt-right (sample-id "Corr_KEM" "ENC_and_DEC" "encaps_rand"))
      (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
    )
  )
)

(define-fun randomness-mapping-TestSender (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "TestSender" "encapsulated_key"))
    (= stmt-right (sample-id "Corr_reduction" "TestSender" "encapsulated_key"))
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)

(define-fun randomness-mapping-TestReceiver (
  (base-ctr-left Int) 
  (base-ctr-right Int)
  (stmt-left  SampleId) 
  (stmt-right  SampleId)
  (ctr-left Int)
  (ctr-right Int)
) Bool
; BEGIN FUNCTION BODY
  (and
    (= stmt-left (sample-id "Prot" "TestReceiver" "encapsulated_key"))
    (= stmt-right (sample-id "Corr_reduction" "TestReceiver" "encapsulated_key"))
    (= (- ctr-left base-ctr-left) (- ctr-right base-ctr-right))
  )
)
