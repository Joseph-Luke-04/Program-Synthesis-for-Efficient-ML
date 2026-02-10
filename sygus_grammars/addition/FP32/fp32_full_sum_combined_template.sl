(set-logic BV)

; ===============================================================
; Monolithic grammar for an approximate FP32 adder (normals-only).
; Normalization is intentionally limited (0/1 step) to keep grammar small.
; ===============================================================

(synth-fun fp32_sum
  ((s1 (_ BitVec 1)) (e1 (_ BitVec 8)) (m1 (_ BitVec 23))
   (s2 (_ BitVec 1)) (e2 (_ BitVec 8)) (m2 (_ BitVec 23)))
  (_ BitVec 32)
  (
    (Start32 (_ BitVec 32))

    (Ma (_ BitVec 24)) (Mb (_ BitVec 24))
    (Swap Bool)

    (Sbig (_ BitVec 1)) (Ssmall (_ BitVec 1))
    (Ebig (_ BitVec 8)) (Esmall (_ BitVec 8))
    (Mbig (_ BitVec 24)) (Msmall (_ BitVec 24))

    (Diff8 (_ BitVec 8))
    (Diff6 (_ BitVec 6))
    (TooBig Bool)
    (Sh27 (_ BitVec 27))

    (Big27 (_ BitVec 27))
    (Small27 (_ BitVec 27))
    (ASmall27 (_ BitVec 27))

    ; NEW: “did we lose bits in the alignment shift?”
    (Back27 (_ BitVec 27))
    (Lost1 (_ BitVec 1))

    (SameSign Bool)
    (Raw28 (_ BitVec 28))

    (Ov1 (_ BitVec 1))
    (N1 (_ BitVec 28))

    (LAmt2 (_ BitVec 2))
    (LAmt28 (_ BitVec 28))
    (N2 (_ BitVec 28))

    (IsZero Bool)

    (Top24 (_ BitVec 24))
    (G (_ BitVec 1)) (R (_ BitVec 1)) (S (_ BitVec 1))
    (LSB (_ BitVec 1))
    (Inc1 (_ BitVec 1))
    (Rounded25 (_ BitVec 25))
    (Frac23 (_ BitVec 23))

    (Adj10 (_ BitVec 10))
    (E10 (_ BitVec 10))
    (Eout (_ BitVec 8))

    (Sout (_ BitVec 1))
  )
  (
    (Start32 (_ BitVec 32) (
      (concat Sout (concat Eout Frac23))
    ))

    ; hidden-1 mantissas (normals-only)
    (Ma (_ BitVec 24) ((concat #b1 m1)))
    (Mb (_ BitVec 24) ((concat #b1 m2)))

    ; "big" select (exp then mant tie-break)
    (Swap Bool (
      (or (bvult e1 e2)
          (and (= e1 e2) (bvult Ma Mb)))
    ))

    (Sbig   (_ BitVec 1) ((ite Swap s2 s1)))
    (Ssmall (_ BitVec 1) ((ite Swap s1 s2)))
    (Ebig   (_ BitVec 8) ((ite Swap e2 e1)))
    (Esmall (_ BitVec 8) ((ite Swap e1 e2)))
    (Mbig   (_ BitVec 24) ((ite Swap Mb Ma)))
    (Msmall (_ BitVec 24) ((ite Swap Ma Mb)))

    ; exponent gap
    (Diff8 (_ BitVec 8) ((bvsub Ebig Esmall)))
    (Diff6 (_ BitVec 6) (((_ extract 5 0) Diff8)))

    ; clamp huge gaps: if shift >= 27 then aligned-small becomes “sticky-only”
    (TooBig Bool ((bvugt Diff6 (_ bv26 6))))
    (Sh27 (_ BitVec 27) (((_ zero_extend 21) Diff6)))

    (Big27   (_ BitVec 27) ((concat Mbig   #b000)))
    (Small27 (_ BitVec 27) ((concat Msmall #b000)))

    ; IMPORTANT CHANGE:
    ; if TooBig, allow either 0 (drop) OR 1 (sticky survives) for ASmall27
    (ASmall27 (_ BitVec 27) (
      (ite TooBig (_ bv0 27) (bvlshr Small27 Sh27))
      (ite TooBig (_ bv1 27) (bvlshr Small27 Sh27))
    ))

    ; NEW: shift back and compare to detect lost bits in alignment
    (Back27 (_ BitVec 27) ((bvshl ASmall27 Sh27)))
    (Lost1 (_ BitVec 1) ((ite (= Back27 Small27) #b0 #b1)))

    (SameSign Bool ((= Sbig Ssmall)))

    (Raw28 (_ BitVec 28) (
      (ite SameSign
        (bvadd ((_ zero_extend 1) Big27) ((_ zero_extend 1) ASmall27))
        (bvsub ((_ zero_extend 1) Big27) ((_ zero_extend 1) ASmall27)))
    ))

    ; overflow normalize
    (Ov1 (_ BitVec 1) (((_ extract 27 27) Raw28)))
    (N1 (_ BitVec 28) ((ite (= Ov1 #b1) (bvlshr Raw28 (_ bv1 28)) Raw28)))

    ; tiny LZC-lite: 0/1/2 left shifts
    (LAmt2 (_ BitVec 2) (
      #b00
      #b01
      #b10
      (ite (= ((_ extract 26 25) N1) #b00) #b10
        (ite (= ((_ extract 26 26) N1) #b0) #b01 #b00))
    ))
    (LAmt28 (_ BitVec 28) (((_ zero_extend 26) LAmt2)))
    (N2 (_ BitVec 28) ((bvshl N1 LAmt28)))

    (IsZero Bool ((= N2 (_ bv0 28))))

    ; mantissa + G/R/S
    (Top24 (_ BitVec 24) (((_ extract 26 3) N2)))
    (G (_ BitVec 1) (((_ extract 2 2) N2)))
    (R (_ BitVec 1) (((_ extract 1 1) N2)))

    ; KEY CHANGE: S includes Lost1 from alignment shift-out
    (S (_ BitVec 1) (
      (bvor ((_ extract 0 0) N2) Lost1)
      (bvor (bvor ((_ extract 0 0) N2) R) Lost1)
    ))

    (LSB (_ BitVec 1) (((_ extract 0 0) Top24)))

    (Inc1 (_ BitVec 1) (
      #b0
      (bvand G (bvor R S))
      (bvand G (bvor R (bvor S LSB)))
    ))

    (Rounded25 (_ BitVec 25) (
      (bvadd ((_ zero_extend 1) Top24) ((_ zero_extend 24) Inc1))
    ))

    (Frac23 (_ BitVec 23) (
      (ite IsZero
        (_ bv0 23)
        ((_ extract 22 0) ((_ extract 23 0) Rounded25)))
    ))

    ; exponent update: +Ov1 - LAmt2 (still approx, but now realizable more often)
    (Adj10 (_ BitVec 10) (
      (bvsub (ite (= Ov1 #b1) (_ bv1 10) (_ bv0 10))
             ((_ zero_extend 8) LAmt2))
    ))
    (E10 (_ BitVec 10) ((bvadd ((_ zero_extend 2) Ebig) Adj10)))
    (Eout (_ BitVec 8) ((ite IsZero (_ bv0 8) ((_ extract 7 0) E10))))

    ; sign: big’s sign, but if exact zero => +0
    (Sout (_ BitVec 1) ((ite IsZero #b0 Sbig)))
  )
)
