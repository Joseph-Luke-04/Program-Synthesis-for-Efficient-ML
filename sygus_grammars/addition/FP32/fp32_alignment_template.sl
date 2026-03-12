(set-logic BV)

; ===============================================================
; FP32 addition alignment — "in-between" structural sketch.
; Compares exponents, shifts the smaller mantissa right by the
; gap, and returns (aligned_m1[23:0], aligned_m2[23:0], target_exp[7:0]).
; Search space ≈ 480 combinations.
; Cmp(4) × Gap8(2) × Shifted24(3) × OutM1(2) × OutM2(2) × OutExp(5) = 480
; ===============================================================

; Structural helper: prepend hidden bit (definitional, not synthesised).
(define-fun fp32_hidden1 ((m (_ BitVec 23))) (_ BitVec 24)
  (concat #b1 m))

(synth-fun fp32_aligner
    ((e1 (_ BitVec 8)) (m1 (_ BitVec 23))
     (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
     (_ BitVec 56)

    (
        (Start56   (_ BitVec 56))
        (Cmp       Bool)
        (BigE      (_ BitVec 8))
        (SmallE    (_ BitVec 8))
        (BigM24    (_ BitVec 24))
        (SmallM24  (_ BitVec 24))
        (Gap8      (_ BitVec 8))
        (Shifted24 (_ BitVec 24))
        (OutM1     (_ BitVec 24))
        (OutM2     (_ BitVec 24))
        (OutExp    (_ BitVec 8))
    )

    (
    ; Output: (aligned_m1, aligned_m2, target_exponent)
    (Start56 (_ BitVec 56)
      ((concat OutM1 (concat OutM2 OutExp))))

    ; --- Stage 1: Ordering ---
    ; Solver discovers the right comparison operator.
    (Cmp Bool (
      (bvuge e1 e2)
      (bvugt e1 e2)
      (bvsge e1 e2)
      (bvsgt e1 e2)
    ))

    (BigE (_ BitVec 8) (
      (ite Cmp e1 e2)
    ))

    (SmallE (_ BitVec 8) (
      (ite Cmp e2 e1)
    ))

    (BigM24 (_ BitVec 24) (
      (ite Cmp (fp32_hidden1 m1) (fp32_hidden1 m2))
    ))

    (SmallM24 (_ BitVec 24) (
      (ite Cmp (fp32_hidden1 m2) (fp32_hidden1 m1))
    ))

    ; --- Stage 2: Exponent gap ---
    (Gap8 (_ BitVec 8) (
      (bvsub BigE SmallE)
      (bvsub e1 e2)
    ))

    ; --- Stage 3: Shift smaller mantissa ---
    ; Solver discovers shift type.
    (Shifted24 (_ BitVec 24) (
      (bvlshr SmallM24 ((_ zero_extend 16) Gap8))
      (bvashr SmallM24 ((_ zero_extend 16) Gap8))
      (bvshl SmallM24 ((_ zero_extend 16) Gap8))
    ))

    ; --- Stage 4: Re-order back to (m1, m2) input order ---
    (OutM1 (_ BitVec 24) (
      (ite Cmp BigM24 Shifted24)
      (fp32_hidden1 m1)
    ))

    (OutM2 (_ BitVec 24) (
      (ite Cmp Shifted24 BigM24)
      (fp32_hidden1 m2)
    ))

    ; --- Stage 5: Forward exponent ---
    (OutExp (_ BitVec 8) (
      BigE
      SmallE
      e1
      e2
      (ite Cmp e1 e2)
    ))
  )
)
