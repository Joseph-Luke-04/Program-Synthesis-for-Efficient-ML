(set-logic BV)

; =================================================================
; Compose the FP32 multiplier from renorm + exp + mant
; =================================================================

(synth-fun fp32_full_mul
  ((a (_ BitVec 32)) (b (_ BitVec 32)))
  (_ BitVec 32)

  (
    (Start32 (_ BitVec 32))

    (Sa   (_ BitVec 1))
    (Sb   (_ BitVec 1))
    (Ea   (_ BitVec 8))
    (Eb   (_ BitVec 8))
    (Fa   (_ BitVec 23))
    (Fb   (_ BitVec 23))
    (Sout (_ BitVec 1))

    (Ma   (_ BitVec 24))
    (Mb   (_ BitVec 24))

    (Ren  (_ BitVec 1))

    (MantPack (_ BitVec 23)) ; frac23
    (Carry    (_ BitVec 1))
    (FracOut  (_ BitVec 23))

    (Eout (_ BitVec 8))
  )

  (
    ; Final packing: sign || exponent || fraction
    (Start32 (_ BitVec 32)
      ((concat Sout (concat Eout FracOut))))

    ; Unpack
    (Sa (_ BitVec 1) (((_ extract 31 31) a)))
    (Sb (_ BitVec 1) (((_ extract 31 31) b)))
    (Ea (_ BitVec 8) (((_ extract 30 23) a)))
    (Eb (_ BitVec 8) (((_ extract 30 23) b)))
    (Fa (_ BitVec 23) (((_ extract 22 0) a)))
    (Fb (_ BitVec 23) (((_ extract 22 0) b)))

    ; Sign of product (normals-only path)
    (Sout (_ BitVec 1)
      ((bvxor Sa Sb)))

    ; Build 24-bit mantissas with implicit leading 1 (normals-only)
    (Ma (_ BitVec 24)
      ((concat #b1 Fa)))
    (Mb (_ BitVec 24)
      ((concat #b1 Fb)))

    ; Stage 1: renormalisation decision
    (Ren (_ BitVec 1)
      ((fp32_mult_renorm Ma Mb)))

    ; Stage 2: mantissa rounding (returns frac23)
    (MantPack (_ BitVec 23)
      ((fp32_mult_mant Ma Mb Ren)))
    (Carry (_ BitVec 1)
      (#b0))
    (FracOut (_ BitVec 23)
      (MantPack))

    ; Stage 3: exponent (depends on renorm and rounding carry)
    (Eout (_ BitVec 8)
      ((fp32_mult_exp Ea Eb Ren Carry)))
  )
)
