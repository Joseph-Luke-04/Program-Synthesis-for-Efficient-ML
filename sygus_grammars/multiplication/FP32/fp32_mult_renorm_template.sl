(set-logic BV)

; ===============================================================
; FP32 multiplication renorm flag — "in-between" structural sketch.
; Detects whether the 48-bit mantissa product requires renormalisation
; (i.e., the product is >= 2.0 in Q1.47 fixed-point).
; Search space ≈ 90 combinations.
; Prod48(1) × DetectBit(3) × Threshold48(3) × Cmp(5) × Start1(2) = 90
; ===============================================================

(define-fun fp32_mult_raw48_renorm ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(synth-fun fp32_mult_renorm
  ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)))
  (_ BitVec 1)

  (
    (Start1      (_ BitVec 1))
    (Prod48      (_ BitVec 48))
    (DetectBit   (_ BitVec 1))
    (Threshold48 (_ BitVec 48))
    (Cmp         Bool)
  )
  (
    ; --- Output ---
    (Start1 (_ BitVec 1) (
      (ite Cmp #b1 #b0)
      DetectBit
    ))

    ; --- Stage 1: Raw product ---
    (Prod48 (_ BitVec 48) (
      (fp32_mult_raw48_renorm Ma Mb)
    ))

    ; --- Stage 2: Direct bit extraction ---
    (DetectBit (_ BitVec 1) (
      ((_ extract 47 47) Prod48)
      ((_ extract 46 46) Prod48)
      ((_ extract 45 45) Prod48)
    ))

    ; --- Stage 3: Threshold for comparison ---
    (Threshold48 (_ BitVec 48) (
      (bvshl (_ bv1 48) (_ bv47 48))
      (bvshl (_ bv1 48) (_ bv46 48))
      (bvshl (_ bv1 48) (_ bv45 48))
    ))

    ; --- Stage 4: Comparison strategy ---
    (Cmp Bool (
      (= DetectBit #b1)
      (bvuge Prod48 Threshold48)
      (bvugt Prod48 Threshold48)
      (not (= DetectBit #b0))
      (= ((_ extract 47 47) Prod48) #b1)
    ))
  )
)
