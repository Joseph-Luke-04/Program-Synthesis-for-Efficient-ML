(set-logic BV)

; Inputs:
;   s1, s2: 1-bit signs of the original operands
;   aligned_m1, aligned_m2: 24-bit aligned magnitudes from the aligner
; Output (26 bits total):
;   concat( raw_sign_1[0], raw_sum_mantissa_25[24:0] )

(synth-fun fp32_raw_summer
  ((s1 (_ BitVec 1)) (aligned_m1 (_ BitVec 24))
   (s2 (_ BitVec 1)) (aligned_m2 (_ BitVec 24)))
  (_ BitVec 26)

  (
    (Start      (_ BitVec 26))
    (RawMant    (_ BitVec 25))
    (RawSign    (_ BitVec 1))
    (SEqual     Bool)
    (M1_GE_M2   Bool)
    (OppSigns   Bool)
    (EqMant     Bool)
  )

  (
    ; 1 - Pack the result
    (Start (_ BitVec 26)
      ((concat RawSign RawMant)))

    ; 2 - Magnitude arithmetic (extend to 25 bits)
    (RawMant (_ BitVec 25)
      ((ite SEqual
            (bvadd (concat #b0 aligned_m1) (concat #b0 aligned_m2))
            (ite M1_GE_M2
                 (bvsub (concat #b0 aligned_m1) (concat #b0 aligned_m2))
                 (bvsub (concat #b0 aligned_m2) (concat #b0 aligned_m1))))))

    ; 3 - Sign selection (force 0 when exact cancellation)
    (RawSign (_ BitVec 1)
      ((ite (and OppSigns EqMant)
            #b0
            (ite SEqual
                 s1
                 (ite M1_GE_M2 s1 s2)))))

    ; 4 - Helpers 
    (SEqual   Bool ((= s1 s2)))
    (M1_GE_M2 Bool ((bvuge aligned_m1 aligned_m2)))
    (OppSigns Bool ((not SEqual)))
    (EqMant   Bool ((= aligned_m1 aligned_m2)))
  )
)
