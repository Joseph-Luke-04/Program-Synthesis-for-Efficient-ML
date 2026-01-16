(set-logic BV)

; =================================================================

; Inputs:
;   e1: 8-bit exponent of operand 1
;   m1: 23-bit mantissa (no hidden 1) of operand 1
;   e2: 8-bit exponent of operand 2
;   m2: 23-bit mantissa (no hidden 1) of operand 2
; Output (56 bits total):
;   concat( aligned_m1_24[23:0], aligned_m2_24[23:0], target_exp_8[7:0] )

; =================================================================

(synth-fun fp32_aligner 
    ((e1 (_ BitVec 8)) (m1 (_ BitVec 23))
     (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
     (_ BitVec 56)

    (
        (Start     (_ BitVec 56))
        (AlignedM1 (_ BitVec 24))
        (AlignedM2 (_ BitVec 24))
        (M1Full    (_ BitVec 24))
        (M2Full    (_ BitVec 24))
        (H1        (_ BitVec 1))
        (H2        (_ BitVec 1))
        (ShiftAmt8 (_ BitVec 8))
        (ShiftAmt24 (_ BitVec 24))
        (TargetExp (_ BitVec 8))
        (E1_GE_E2  Bool)
    )

    (
    ; 1 - Final packing
    (Start (_ BitVec 56)
      ((concat AlignedM1 (concat AlignedM2 TargetExp))))

    ; 2 - Aligned mantissa for operand 1
    (AlignedM1 (_ BitVec 24)
      ((ite E1_GE_E2
            M1Full
            (bvlshr M1Full ShiftAmt24))))

    ; 3 - Aligned mantissa for operand 2
    (AlignedM2 (_ BitVec 24)
      ((ite E1_GE_E2
            (bvlshr M2Full ShiftAmt24)
            M2Full)))

    ; 4 - m1 with hidden bit (0 if e1 == 0 for subnormals/zeros)
    (M1Full (_ BitVec 24)
      ((concat H1 m1)))

    ; 5 - m2 with hidden bit (0 if e2 == 0 for subnormals/zeros)
    (M2Full (_ BitVec 24)
      ((concat H2 m2)))

    ; 6 - hidden bit for m1
    (H1 (_ BitVec 1)
      ((ite (= e1 #x00) #b0 #b1)))

    ; 7 - hidden bit for m2
    (H2 (_ BitVec 1)
      ((ite (= e2 #x00) #b0 #b1)))

    ; 8 - 8-bit unsigned exponent difference (absolute)
    (ShiftAmt8 (_ BitVec 8)
      ((ite E1_GE_E2 (bvsub e1 e2) (bvsub e2 e1))))

    ; 9 - Zero-extend to 24 bits for shifts on 24-bit mantissas
    (ShiftAmt24 (_ BitVec 24)
      ((concat (_ bv0 16) ShiftAmt8)))

    ; 10 - Choose larger exponent
    (TargetExp (_ BitVec 8)
      ((ite E1_GE_E2 e1 e2)))

    ; 11 - Unsigned compare e1 >= e2
    (E1_GE_E2 Bool
      ((bvuge e1 e2)))
  )
)
