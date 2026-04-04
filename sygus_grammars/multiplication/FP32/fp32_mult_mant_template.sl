(set-logic BV)

; ===============================================================
; FP32 multiplication mantissa
; Multiplies two 24-bit mantissas (with hidden bit), conditionally
; shifts based on renorm flag, and extracts the 23-bit fraction.
; ===============================================================

; Structural helper: the raw product (definitional, not synthesised).
(define-fun fp32_mult_raw48 ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(synth-fun fp32_mult_mant
  ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)) (renorm (_ BitVec 1)))
  (_ BitVec 23)

  (
    (Start23       (_ BitVec 23))
    (Prod48        (_ BitVec 48))
    (ShiftedProd48 (_ BitVec 48))
    (Extract24     (_ BitVec 24))
    (Guard1        (_ BitVec 1))
    (Round1        (_ BitVec 1))
    (RoundUp       Bool)
    (Rounded24     (_ BitVec 24))
    (Out23         (_ BitVec 23))
  )
  (
    ; Output 
    (Start23 (_ BitVec 23) (
      Out23
    ))

    ; Raw product
    (Prod48 (_ BitVec 48) (
      (fp32_mult_raw48 Ma Mb)
    ))

    ; Conditional shift for renormalisation
    (ShiftedProd48 (_ BitVec 48) (
      (ite (= renorm #b1) (bvlshr Prod48 (_ bv1 48)) Prod48)
      (bvlshr Prod48 ((_ zero_extend 47) renorm))
      Prod48
    ))

    ; Extract 24-bit mantissa (including hidden bit)
    ; Different extraction windows depending on product format.
    (Extract24 (_ BitVec 24) (
      ((_ extract 46 23) ShiftedProd48)
      ((_ extract 45 22) ShiftedProd48)
      ((_ extract 47 24) ShiftedProd48)
    ))

    ; Rounding bits
    (Guard1 (_ BitVec 1) (
      ((_ extract 22 22) ShiftedProd48)
      ((_ extract 22 22) Prod48)
      ((_ extract 23 23) ShiftedProd48)
    ))

    (Round1 (_ BitVec 1) (
      ((_ extract 21 21) ShiftedProd48)
      ((_ extract 21 21) Prod48)
      ((_ extract 22 22) ShiftedProd48)
    ))

    ; Rounding decision
    (RoundUp Bool (
      (= Guard1 #b1)
      (and (= Guard1 #b1) (= Round1 #b1))
      (and (= Guard1 #b1) (or (= Round1 #b1) (= ((_ extract 0 0) Extract24) #b1)))
    ))

    ; Apply rounding 
    (Rounded24 (_ BitVec 24) (
      (ite RoundUp (bvadd Extract24 (_ bv1 24)) Extract24)
      Extract24
      (bvadd Extract24 ((_ zero_extend 23) Guard1))
    ))

    ; Strip hidden bit
    (Out23 (_ BitVec 23) (
      ((_ extract 22 0) Rounded24)
      ((_ extract 22 0) Extract24)
    ))
  )
)
