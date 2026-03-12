(set-logic BV)

; ===============================================================
; FP32 addition raw sum — "in-between" structural sketch.
; Takes sign-magnitude aligned operands and computes the raw
; signed-magnitude sum: (result_sign, |result|[24:0]).
; Search space ≈ 288 combinations.
; SameSign(2) × M1Bigger(3) × SumSame25(3) × Diff25(2) × Mag25(2) × SignOut(4) = 288
; ===============================================================

(synth-fun fp32_raw_summer
  ((s1 (_ BitVec 1)) (aligned_m1 (_ BitVec 24))
   (s2 (_ BitVec 1)) (aligned_m2 (_ BitVec 24)))
  (_ BitVec 26)

  (
    (Start26    (_ BitVec 26))
    (SameSign   Bool)

    ; same-sign path: magnitudes add
    (SumSame25  (_ BitVec 25))

    ; opposite-sign path: magnitudes subtract (big - small)
    (M1Bigger   Bool)
    (BigM       (_ BitVec 24))
    (SmallM     (_ BitVec 24))
    (Diff25     (_ BitVec 25))

    ; mux based on same/opposite sign
    (Mag25      (_ BitVec 25))

    ; result sign
    (SignOut     (_ BitVec 1))
  )

  (
    (Start26 (_ BitVec 26) (
      (concat SignOut Mag25)
    ))

    ; --- Stage 1: Are the signs the same? ---
    (SameSign Bool (
      (= s1 s2)
      (not (= s1 s2))
    ))

    ; --- Stage 2a: Same-sign path (add magnitudes) ---
    (SumSame25 (_ BitVec 25) (
      (bvadd ((_ zero_extend 1) aligned_m1) ((_ zero_extend 1) aligned_m2))
      (bvadd ((_ sign_extend 1) aligned_m1) ((_ sign_extend 1) aligned_m2))
      (bvor  ((_ zero_extend 1) aligned_m1) ((_ zero_extend 1) aligned_m2))
    ))

    ; --- Stage 2b: Opposite-sign path (subtract magnitudes) ---
    (M1Bigger Bool (
      (bvuge aligned_m1 aligned_m2)
      (bvugt aligned_m1 aligned_m2)
      (bvsge aligned_m1 aligned_m2)
    ))

    (BigM (_ BitVec 24) (
      (ite M1Bigger aligned_m1 aligned_m2)
    ))

    (SmallM (_ BitVec 24) (
      (ite M1Bigger aligned_m2 aligned_m1)
    ))

    (Diff25 (_ BitVec 25) (
      (bvsub ((_ zero_extend 1) BigM) ((_ zero_extend 1) SmallM))
      ((_ zero_extend 1) (bvsub BigM SmallM))
    ))

    ; --- Stage 3: Select magnitude based on sign comparison ---
    (Mag25 (_ BitVec 25) (
      (ite SameSign SumSame25 Diff25)
      SumSame25
    ))

    ; --- Stage 4: Determine result sign ---
    ; Same sign: inherit s1 or s2. Opposite sign: sign of bigger magnitude.
    (SignOut (_ BitVec 1) (
      (ite SameSign s1 (ite M1Bigger s1 s2))
      (ite SameSign s2 (ite M1Bigger s1 s2))
      s1
      (ite (= s1 #b1)
           (ite M1Bigger #b1 #b0)
           (ite M1Bigger #b0 #b1))
    ))
  )
)
