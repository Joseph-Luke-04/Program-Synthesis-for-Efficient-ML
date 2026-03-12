(set-logic BV)

; ===============================================================
; MXINT8 addition alignment — V2 "structural sketch" grammar.
; Two synth-funs: select_exponent picks the larger exponent,
; align_mantissas shifts the smaller mantissa into alignment.
; Encodes the pipeline (compare → order → round → shift → reorder)
; but leaves implementation choices open for the solver.
; Search space ≈ 192 combinations (vs V1 recursive ≈ infinite).
; ===============================================================

; ---------------------------------------------------------------
; select_exponent: return max(e1, e2) in signed 4-bit
; Search space: 2 comparisons × 2 orderings = 4 combinations
; ---------------------------------------------------------------
(synth-fun select_exponent
    ((e1 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 4)
    (
        (Start4 (_ BitVec 4))
        (Cmp    Bool)
    )
    (
      (Start4 (_ BitVec 4) (
        (ite Cmp e1 e2)
        (ite Cmp e2 e1)
      ))

      (Cmp Bool (
        (bvsge e1 e2)
        (bvsgt e1 e2)
      ))
    )
)

; ---------------------------------------------------------------
; align_mantissas: shift the smaller mantissa right by the
; exponent gap, return (aligned_m1 ++ aligned_m2) as 8-bit.
; Output is ALWAYS in (m1, m2) input order.
;
; Choices:  Cmp(2) × BigM(2) × SmallM(2) × Bias4(3)
;         × SignedBias5(2) × Rounded5(2) × AlignedS(2)
;         × OutM1(2) × OutM2(2) = 192
; ---------------------------------------------------------------
(synth-fun align_mantissas
    ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
    (_ BitVec 8)
    (
        (Start8      (_ BitVec 8))
        (Cmp         Bool)
        (BigM        (_ BitVec 4))
        (SmallM      (_ BitVec 4))
        (SmallE      (_ BitVec 4))
        (Gap5        (_ BitVec 5))
        (Gap4        (_ BitVec 4))
        (Bias4       (_ BitVec 4))
        (SignedBias5 (_ BitVec 5))
        (Rounded5    (_ BitVec 5))
        (Shifted4    (_ BitVec 4))
        (AlignedS    (_ BitVec 4))
        (OutM1       (_ BitVec 4))
        (OutM2       (_ BitVec 4))
    )
    (
      (Start8 (_ BitVec 8) (
        (concat OutM1 OutM2)
      ))

      ; --- Stage 1: Ordering ---
      (Cmp Bool (
        (bvsge e1 e2)
        (bvsgt e1 e2)
      ))

      (BigM (_ BitVec 4) (
        (ite Cmp m1 m2)
        (ite Cmp m2 m1)
      ))

      (SmallM (_ BitVec 4) (
        (ite Cmp m2 m1)
        (ite Cmp m1 m2)
      ))

      (SmallE (_ BitVec 4) (
        (ite Cmp e2 e1)
      ))

      ; --- Stage 2: Exponent gap (fixed, no ambiguity needed here) ---
      (Gap5 (_ BitVec 5) (
        (bvsub ((_ sign_extend 1) (ite Cmp e1 e2))
               ((_ sign_extend 1) SmallE))
      ))

      (Gap4 (_ BitVec 4) (
        ((_ extract 3 0) Gap5)
      ))

      ; --- Stage 3: Optional rounding bias before shift ---
      (Bias4 (_ BitVec 4) (
        (ite (= Gap4 #b0001) #b0001
             (ite (= Gap4 #b0010) #b0010
                  (ite (= Gap4 #b0011) #b0100 #b0000)))
        Gap4
        #b0000
      ))

      (SignedBias5 (_ BitVec 5) (
        ((_ sign_extend 1)
         (ite (bvslt SmallM #b0000) (bvneg Bias4) Bias4))
        ((_ sign_extend 1) Bias4)
      ))

      (Rounded5 (_ BitVec 5) (
        (bvadd ((_ sign_extend 1) SmallM) SignedBias5)
        ((_ sign_extend 1) SmallM)
      ))

      ; --- Stage 4: Shift (always arithmetic, mantissas are signed) ---
      (Shifted4 (_ BitVec 4) (
        ((_ extract 3 0) (bvashr Rounded5 Gap5))
      ))

      ; Flush to zero when gap is large enough.
      (AlignedS (_ BitVec 4) (
        (ite (bvsge Gap5 #b00100) #b0000 Shifted4)
        Shifted4
      ))

      ; --- Stage 5: Re-order back to (m1, m2) input order ---
      (OutM1 (_ BitVec 4) (
        (ite Cmp BigM AlignedS)
        (ite Cmp AlignedS BigM)
      ))

      (OutM2 (_ BitVec 4) (
        (ite Cmp AlignedS BigM)
        (ite Cmp BigM AlignedS)
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var e1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))
(declare-var e2 (_ BitVec 4))
