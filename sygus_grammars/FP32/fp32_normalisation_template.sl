(set-logic BV)

; Inputs:
;   raw_sum_mantissa: 25-bit unsigned magnitude from raw summer
;   raw_sign: 1-bit sign from raw summer
;   target_exponent: 8-bit exponent chosen during alignment
; Outputs (32 bits total):
;   concat( final_sign[0], final_exponent_8[7:0], final_mantissa_23[22:0] )

(synth-fun fp32_normaliser
  ((raw_sum_mantissa (_ BitVec 25))
   (raw_sign        (_ BitVec 1))
   (target_exponent (_ BitVec 8)))
  (_ BitVec 32)

  (
    (Start     (_ BitVec 32))
    (FinalSign (_ BitVec 1))
    (FinalExp  (_ BitVec 8))
    (FinalMant (_ BitVec 23))
    (Norm24    (_ BitVec 24))
    (ExpDelta  (_ BitVec 8))

    (IsZero    Bool)
    (B24 Bool) (B23 Bool) (B22 Bool) (B21 Bool) (B20 Bool)
    (B19 Bool) (B18 Bool) (B17 Bool) (B16 Bool) (B15 Bool)
    (B14 Bool) (B13 Bool) (B12 Bool) (B11 Bool) (B10 Bool)
    (B09 Bool) (B08 Bool) (B07 Bool) (B06 Bool) (B05 Bool)
    (B04 Bool) (B03 Bool) (B02 Bool) (B01 Bool) (B00 Bool)
  )

  (
    ; 1 - Pack final IEEE754 components (no rounding; just normalise)
    (Start (_ BitVec 32)
      ((concat FinalSign (concat FinalExp FinalMant))))

    ; 2 - Final sign: zero result forces +0
    (FinalSign (_ BitVec 1)
      ((ite IsZero #b0 raw_sign)))

    ; 3 - Final exponent: target_exponent + shift delta (two's complement)
    (FinalExp (_ BitVec 8)
      ((ite IsZero
            (_ bv0 8)
            (bvadd target_exponent ExpDelta))))

    ; 4 - Final mantissa: drop hidden bit after normalising to 24-bit
    (FinalMant (_ BitVec 23)
      (((_ extract 22 0) Norm24)))

    ; 5 - Normalised 24-bit magnitude
    ;    Priority encode highest set bit of raw_sum_mantissa, then shift
    ;    so that hidden '1' lands at bit 23.
    (Norm24 (_ BitVec 24)
      ((ite B24 ((_ extract 24 1) raw_sum_mantissa)                                 ; >>1
       (ite B23 ((_ extract 23 0) raw_sum_mantissa)                                  ;  no shift
       (ite B22 (concat ((_ extract 22 0) raw_sum_mantissa) (_ bv0 1))               ; <<1
       (ite B21 (concat ((_ extract 21 0) raw_sum_mantissa) (_ bv0 2))               ; <<2
       (ite B20 (concat ((_ extract 20 0) raw_sum_mantissa) (_ bv0 3))               ; <<3
       (ite B19 (concat ((_ extract 19 0) raw_sum_mantissa) (_ bv0 4))
       (ite B18 (concat ((_ extract 18 0) raw_sum_mantissa) (_ bv0 5))
       (ite B17 (concat ((_ extract 17 0) raw_sum_mantissa) (_ bv0 6))
       (ite B16 (concat ((_ extract 16 0) raw_sum_mantissa) (_ bv0 7))
       (ite B15 (concat ((_ extract 15 0) raw_sum_mantissa) (_ bv0 8))
       (ite B14 (concat ((_ extract 14 0) raw_sum_mantissa) (_ bv0 9))
       (ite B13 (concat ((_ extract 13 0) raw_sum_mantissa) (_ bv0 10))
       (ite B12 (concat ((_ extract 12 0) raw_sum_mantissa) (_ bv0 11))
       (ite B11 (concat ((_ extract 11 0) raw_sum_mantissa) (_ bv0 12))
       (ite B10 (concat ((_ extract 10 0) raw_sum_mantissa) (_ bv0 13))
       (ite B09 (concat ((_ extract 9 0)  raw_sum_mantissa) (_ bv0 14))
       (ite B08 (concat ((_ extract 8 0)  raw_sum_mantissa) (_ bv0 15))
       (ite B07 (concat ((_ extract 7 0)  raw_sum_mantissa) (_ bv0 16))
       (ite B06 (concat ((_ extract 6 0)  raw_sum_mantissa) (_ bv0 17))
       (ite B05 (concat ((_ extract 5 0)  raw_sum_mantissa) (_ bv0 18))
       (ite B04 (concat ((_ extract 4 0)  raw_sum_mantissa) (_ bv0 19))
       (ite B03 (concat ((_ extract 3 0)  raw_sum_mantissa) (_ bv0 20))
       (ite B02 (concat ((_ extract 2 0)  raw_sum_mantissa) (_ bv0 21))
       (ite B01 (concat ((_ extract 1 0)  raw_sum_mantissa) (_ bv0 22))
       (ite B00 (concat ((_ extract 0 0)  raw_sum_mantissa) (_ bv0 23))
                (_ bv0 24))))))))))))))))))))))))))))

    ; 6 - Exponent delta corresponding to the chosen normalisation
    ;    +1 if carry into bit 24, 0 if already at bit 23, otherwise negative.
    (ExpDelta (_ BitVec 8)
      ((ite B24 (_ bv1 8)
       (ite B23 (_ bv0 8)
       (ite B22 (bvneg (_ bv1 8))
       (ite B21 (bvneg (_ bv2 8))
       (ite B20 (bvneg (_ bv3 8))
       (ite B19 (bvneg (_ bv4 8))
       (ite B18 (bvneg (_ bv5 8))
       (ite B17 (bvneg (_ bv6 8))
       (ite B16 (bvneg (_ bv7 8))
       (ite B15 (bvneg (_ bv8 8))
       (ite B14 (bvneg (_ bv9 8))
       (ite B13 (bvneg (_ bv10 8))
       (ite B12 (bvneg (_ bv11 8))
       (ite B11 (bvneg (_ bv12 8))
       (ite B10 (bvneg (_ bv13 8))
       (ite B09 (bvneg (_ bv14 8))
       (ite B08 (bvneg (_ bv15 8))
       (ite B07 (bvneg (_ bv16 8))
       (ite B06 (bvneg (_ bv17 8))
       (ite B05 (bvneg (_ bv18 8))
       (ite B04 (bvneg (_ bv19 8))
       (ite B03 (bvneg (_ bv20 8))
       (ite B02 (bvneg (_ bv21 8))
       (ite B01 (bvneg (_ bv22 8))
       (ite B00 (bvneg (_ bv23 8))
                (_ bv0 8))))))))))))))))))))))))))))

    ; 7 - Bit detectors (priority is B24 .. B00)
    (IsZero Bool ((= raw_sum_mantissa (_ bv0 25))))
    (B24 Bool ((= ((_ extract 24 24) raw_sum_mantissa) #b1)))
    (B23 Bool ((= ((_ extract 23 23) raw_sum_mantissa) #b1)))
    (B22 Bool ((= ((_ extract 22 22) raw_sum_mantissa) #b1)))
    (B21 Bool ((= ((_ extract 21 21) raw_sum_mantissa) #b1)))
    (B20 Bool ((= ((_ extract 20 20) raw_sum_mantissa) #b1)))
    (B19 Bool ((= ((_ extract 19 19) raw_sum_mantissa) #b1)))
    (B18 Bool ((= ((_ extract 18 18) raw_sum_mantissa) #b1)))
    (B17 Bool ((= ((_ extract 17 17) raw_sum_mantissa) #b1)))
    (B16 Bool ((= ((_ extract 16 16) raw_sum_mantissa) #b1)))
    (B15 Bool ((= ((_ extract 15 15) raw_sum_mantissa) #b1)))
    (B14 Bool ((= ((_ extract 14 14) raw_sum_mantissa) #b1)))
    (B13 Bool ((= ((_ extract 13 13) raw_sum_mantissa) #b1)))
    (B12 Bool ((= ((_ extract 12 12) raw_sum_mantissa) #b1)))
    (B11 Bool ((= ((_ extract 11 11) raw_sum_mantissa) #b1)))
    (B10 Bool ((= ((_ extract 10 10) raw_sum_mantissa) #b1)))
    (B09 Bool ((= ((_ extract 9 9) raw_sum_mantissa) #b1)))
    (B08 Bool ((= ((_ extract 8 8) raw_sum_mantissa) #b1)))
    (B07 Bool ((= ((_ extract 7 7) raw_sum_mantissa) #b1)))
    (B06 Bool ((= ((_ extract 6 6) raw_sum_mantissa) #b1)))
    (B05 Bool ((= ((_ extract 5 5) raw_sum_mantissa) #b1)))
    (B04 Bool ((= ((_ extract 4 4) raw_sum_mantissa) #b1)))
    (B03 Bool ((= ((_ extract 3 3) raw_sum_mantissa) #b1)))
    (B02 Bool ((= ((_ extract 2 2) raw_sum_mantissa) #b1)))
    (B01 Bool ((= ((_ extract 1 1) raw_sum_mantissa) #b1)))
    (B00 Bool ((= ((_ extract 0 0) raw_sum_mantissa) #b1)))
  )
)
