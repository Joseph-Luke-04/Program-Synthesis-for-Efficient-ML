(set-logic BV)

; =================================================================
; Synthesize the composed FP32 adder
; =================================================================

(synth-fun fp32_sum
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)

  (
    (Start32  (_ BitVec 32))
    (AlignOut (_ BitVec 56))
    (A1       (_ BitVec 24))
    (A2       (_ BitVec 24))
    (Texp     (_ BitVec 8))
    (RawOut   (_ BitVec 26))
    (Rsign    (_ BitVec 1))
    (Rmant    (_ BitVec 25))
  )

  (
    ; 1 - Final packing: normaliser output
    (Start32 (_ BitVec 32)
      ((fp32_normaliser Rmant Rsign Texp)))

    ; 2 - Stage 1: alignment
    (AlignOut (_ BitVec 56)
      ((fp32_aligner e1 m1 e2 m2)))
    (A1   (_ BitVec 24) (((_ extract 55 32) AlignOut)))
    (A2   (_ BitVec 24) (((_ extract 31 8)  AlignOut)))
    (Texp (_ BitVec 8)  (((_ extract 7  0)  AlignOut)))

    ; 3 - Stage 2: raw sum
    (RawOut (_ BitVec 26)
      ((fp32_raw_summer s1 A1 s2 A2)))
    (Rsign (_ BitVec 1)  (((_ extract 25 25) RawOut)))
    (Rmant (_ BitVec 25) (((_ extract 24  0) RawOut)))
  )
)
