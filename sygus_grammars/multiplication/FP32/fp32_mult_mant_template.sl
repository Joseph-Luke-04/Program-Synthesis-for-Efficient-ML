(set-logic BV)

; Mantissa for normals-only multiply.
; Inputs are 24-bit mantissas (hidden-1 already applied in Python ground truth).
; Output is the 23-bit fraction field after normalisation + rounding.
(synth-fun fp32_mult_mant
  ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)) (renorm (_ BitVec 1)))
  (_ BitVec 23)

  (
    (Start23 (_ BitVec 23))

    (P48     (_ BitVec 48))
    (PN48    (_ BitVec 48))

    (Top24   (_ BitVec 24))
    (MantN23 (_ BitVec 23))

    (G (_ BitVec 1))
    (R (_ BitVec 1))
    (S (_ BitVec 1))
    (LSB (_ BitVec 1))
    (Low21 (_ BitVec 21))

    (Inc1  (_ BitVec 1))
    (Inc24 (_ BitVec 24))
    (Base24 (_ BitVec 24))
    (Sum24 (_ BitVec 24))

    (Cond Bool)
  )
  (
    (Start23 (_ BitVec 23) (
      MantN23
      ((_ extract 22 0) Sum24)
      (bvadd MantN23 ((_ zero_extend 22) Inc1))          ; add inc in 23-bit space
      (bvor  MantN23 ((_ zero_extend 22) Inc1))          ; OR-based variant
      (bvor  MantN23 ((_ zero_extend 22) G))             ; paper-style mant | G
      (ite Cond ((_ extract 22 0) Sum24) MantN23)
    ))

    ; 48-bit product (must widen before multiply!)
    (P48 (_ BitVec 48) (
      (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))
    ))

    ; Apply renorm shift if requested
    (PN48 (_ BitVec 48) (
      (ite (= renorm #b1) (bvlshr P48 (_ bv1 48)) P48)
      P48
      (bvlshr P48 (_ bv1 48))
    ))

    ; Extract [46:23] = 24 bits (hidden 1 + 23 fraction bits)
    (Top24 (_ BitVec 24) (
      ((_ extract 46 23) PN48)
      ((_ extract 45 22) PN48)   ; nearby alternative
    ))

    ; Drop hidden 1 => 23-bit fraction
    (MantN23 (_ BitVec 23) (
      ((_ extract 22 0) Top24)
    ))

    ; GRS from below the kept fraction
    (G (_ BitVec 1) (
      ((_ extract 22 22) PN48)
      ((_ extract 21 21) PN48)
      #b0
      #b1
    ))

    (R (_ BitVec 1) (
      ((_ extract 21 21) PN48)
      ((_ extract 20 20) PN48)
      #b0
      #b1
    ))

    (S (_ BitVec 1) (
      (ite (= Low21 (_ bv0 21)) #b0 #b1)  ; sticky = OR(low bits)
      #b0
      #b1
    ))

    (LSB (_ BitVec 1) (
      ((_ extract 0 0) MantN23)
      G
      R
      #b0
      #b1
    ))

    (Low21 (_ BitVec 21) (
      ((_ extract 20 0) PN48)
    ))

    ; Increment bit candidates (standard RNE is included but not forced)
    (Inc1 (_ BitVec 1) (
      #b0
      #b1
      G
      R
      S
      LSB
      (bvand G (bvor R S))                    ; common
      (bvand G (bvor R (bvor S LSB)))         ; standard RNE-ish increment
      (bvor G R)
      (bvor G (bvor R S))
      (bvxor G LSB)
      (ite Cond #b1 #b0)
    ))

    (Inc24 (_ BitVec 24) (
      ((_ zero_extend 23) Inc1)
      ((_ zero_extend 23) G)
      ((_ zero_extend 23) R)
      ((_ zero_extend 23) S)
      (bvadd ((_ zero_extend 23) G) ((_ zero_extend 23) R))
    ))

    (Base24 (_ BitVec 24) (
      (concat #b0 MantN23)
      (concat G MantN23)             ; lets synth try a “weird” packing variant
    ))

    (Sum24 (_ BitVec 24) (
      (bvadd Base24 Inc24)           ; arithmetic rounding family
      (bvor  Base24 Inc24)           ; OR-based approximation family
      (bvadd Base24 ((_ zero_extend 23) Inc1))
      (bvor  Base24 ((_ zero_extend 23) Inc1))
    ))

    (Cond Bool (
      (= G #b1)
      (= R #b1)
      (= S #b1)
      (and (= G #b1) (or (= R #b1) (= S #b1)))
      (and (= G #b1) (= LSB #b1))
      (or (= R #b1) (= S #b1))
    ))
  )
)