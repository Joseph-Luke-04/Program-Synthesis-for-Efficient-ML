(set-logic BV)

; ===============================================================
; MXINT8 multiplication mantissa — "in-between" structural sketch.
; Multiplies two 4-bit signed mantissas, takes absolute value,
; and extracts the 4-bit result mantissa.
; Solver discovers: abs strategy, shift type/amount, extraction window.
; Search space ≈ 216 combinations (conditional shift doubles ShiftAmt choices).
; Prod8(1) × Abs8(2) × Shifted8(3) × ShiftAmt(6+cond) × Out4(3) ≈ 216
; ===============================================================

(synth-fun mult_mxint_mant ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 4)
  (
    (Start4      (_ BitVec 4))
    (Prod8       (_ BitVec 8))
    (Abs8        (_ BitVec 8))
    (LargeProd   Bool)
    (Shifted8    (_ BitVec 8))
    (ShiftAmt    (_ BitVec 8))
    (Out4        (_ BitVec 4))
  )
  (
    ; --- Output ---
    (Start4 (_ BitVec 4) (
      Out4
    ))

    ; --- Stage 1: Raw signed product ---
    (Prod8 (_ BitVec 8) (
      (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
    ))

    ; --- Stage 2: Absolute value (or skip if not needed) ---
    (Abs8 (_ BitVec 8) (
      (ite (bvslt Prod8 #x00) (bvneg Prod8) Prod8)
      Prod8
    ))

    ; --- Stage 2b: Threshold check for conditional shift ---
    (LargeProd Bool (
      (bvsge Abs8 #x20)  ; |prod| >= 32
      (bvsgt Abs8 #x1F)  ; |prod| > 31 (equivalent)
    ))

    ; --- Stage 3: Shift to extract mantissa bits ---
    (Shifted8 (_ BitVec 8) (
      (bvashr Abs8 ShiftAmt)
      (bvlshr Abs8 ShiftAmt)
      Abs8
    ))

    ; --- Stage 4: Shift amount (conditional is the key option) ---
    (ShiftAmt (_ BitVec 8) (
      (ite LargeProd #x03 #x02)  ; large prod => >>3, small => >>2
      #x01
      #x02
      #x03
      #x04
    ))

    ; --- Stage 5: Extract 4-bit result ---
    (Out4 (_ BitVec 4) (
      ((_ extract 3 0) Shifted8)
      ((_ extract 3 0) Abs8)
      ((_ extract 7 4) Shifted8)
    ))
  )
)
