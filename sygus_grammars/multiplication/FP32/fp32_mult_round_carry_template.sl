(set-logic BV)

; ===============================================================
; FP32 multiplication round-carry — "in-between" structural sketch.
; Detects whether rounding the mantissa product causes a carry
; into the exponent field (i.e., mantissa overflows to all zeros).
; Search space ≈ 216 combinations.
; ShiftedProd48(3) × Extract24(3) × Guard1(2) × Round1(2) × RoundUp(3) × Carry(2) = 216
; ===============================================================

; Structural helper: the raw product (definitional, not synthesised).
(define-fun fp32_mult_raw48_carry ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(synth-fun fp32_mult_round_carry
  ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)) (renorm (_ BitVec 1)))
  (_ BitVec 1)

  (
    (Start1         (_ BitVec 1))
    (Prod48         (_ BitVec 48))
    (ShiftedProd48  (_ BitVec 48))
    (Extract24      (_ BitVec 24))
    (Guard1         (_ BitVec 1))
    (Round1         (_ BitVec 1))
    (RoundUp        Bool)
    (Rounded24      (_ BitVec 24))
    (Carry          Bool)
  )
  (
    ; --- Output ---
    (Start1 (_ BitVec 1) (
      (ite Carry #b1 #b0)
    ))

    ; --- Stage 1: Raw product ---
    (Prod48 (_ BitVec 48) (
      (fp32_mult_raw48_carry Ma Mb)
    ))

    ; --- Stage 2: Conditional shift ---
    (ShiftedProd48 (_ BitVec 48) (
      (ite (= renorm #b1) (bvlshr Prod48 (_ bv1 48)) Prod48)
      (bvlshr Prod48 ((_ zero_extend 47) renorm))
      Prod48
    ))

    ; --- Stage 3: Extract mantissa ---
    (Extract24 (_ BitVec 24) (
      ((_ extract 46 23) ShiftedProd48)
      ((_ extract 45 22) ShiftedProd48)
      ((_ extract 47 24) ShiftedProd48)
    ))

    ; --- Stage 4: Rounding bits ---
    (Guard1 (_ BitVec 1) (
      ((_ extract 22 22) ShiftedProd48)
      ((_ extract 22 22) Prod48)
    ))

    (Round1 (_ BitVec 1) (
      ((_ extract 21 21) ShiftedProd48)
      ((_ extract 21 21) Prod48)
    ))

    ; --- Stage 5: Rounding decision ---
    (RoundUp Bool (
      (= Guard1 #b1)
      (and (= Guard1 #b1) (= Round1 #b1))
      (and (= Guard1 #b1) (or (= Round1 #b1) (= ((_ extract 0 0) Extract24) #b1)))
    ))

    ; --- Stage 6: Check if rounding causes overflow ---
    (Rounded24 (_ BitVec 24) (
      (ite RoundUp (bvadd Extract24 (_ bv1 24)) Extract24)
    ))

    ; --- Stage 7: Detect carry ---
    (Carry Bool (
      (and RoundUp (= ((_ extract 23 23) Rounded24) #b1))
      (and RoundUp (= Extract24 (_ bv16777215 24)))
    ))
  )
)
