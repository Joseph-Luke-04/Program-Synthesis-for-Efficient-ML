(set-logic BV)

; ===============================================================
; FP32 multiplication exponent
; Computes biased result exponent from two input exponents,
; renorm flag, and carry flag.
; Formula: result = ea + eb - bias + renorm + carry (approximately).
; ===============================================================

(synth-fun fp32_mult_exp
  ((ea (_ BitVec 8)) (eb (_ BitVec 8)) (renorm (_ BitVec 1)) (carry (_ BitVec 1)))
  (_ BitVec 8)

  (
    (Start8      (_ BitVec 8))
    (EA10        (_ BitVec 10))
    (EB10        (_ BitVec 10))
    (SumRaw10    (_ BitVec 10))
    (Bias10      (_ BitVec 10))
    (Unbiased10  (_ BitVec 10))
    (Renorm10    (_ BitVec 10))
    (RenormAdj10 (_ BitVec 10))
    (Carry10     (_ BitVec 10))
    (CarryAdj10  (_ BitVec 10))
    (Out8        (_ BitVec 8))
  )
  (
    ; Output: truncate to 8 bits
    (Start8 (_ BitVec 8) (
      Out8
    ))

    ; Extend inputs to 10 bits
    (EA10 (_ BitVec 10) (
      ((_ zero_extend 2) ea)
    ))

    (EB10 (_ BitVec 10) (
      ((_ zero_extend 2) eb)
    ))

    ; Sum the two exponents
    (SumRaw10 (_ BitVec 10) (
      (bvadd EA10 EB10)
      (bvadd ((_ sign_extend 2) ea) ((_ sign_extend 2) eb))
      (bvor EA10 EB10)
    ))

    ; Subtract bias
    (Bias10 (_ BitVec 10) (
      (_ bv127 10)           ; standard IEEE 754 bias
      (_ bv126 10)           ; bias - 1
      (_ bv128 10)           ; bias + 1
      (_ bv0 10)             ; no bias removal
    ))

    (Unbiased10 (_ BitVec 10) (
      (bvsub SumRaw10 Bias10)
      (bvadd SumRaw10 Bias10)
    ))

    ; Renorm adjustment
    (Renorm10 (_ BitVec 10) (
      ((_ zero_extend 9) renorm)
    ))

    (RenormAdj10 (_ BitVec 10) (
      (bvadd Unbiased10 Renorm10)
      (bvsub Unbiased10 Renorm10)
      Unbiased10
    ))

    ; Carry adjustment
    (Carry10 (_ BitVec 10) (
      ((_ zero_extend 9) carry)
    ))

    (CarryAdj10 (_ BitVec 10) (
      (bvadd RenormAdj10 Carry10)
      (bvsub RenormAdj10 Carry10)
      RenormAdj10
    ))

    ; Extract result
    (Out8 (_ BitVec 8) (
      ((_ extract 7 0) CarryAdj10)
      (ite (= renorm #b1)
           ((_ extract 7 0) (bvadd CarryAdj10 (_ bv1 10)))
           ((_ extract 7 0) CarryAdj10))
    ))
  )
)
