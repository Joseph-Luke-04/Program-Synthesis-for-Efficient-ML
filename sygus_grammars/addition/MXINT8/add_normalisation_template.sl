(set-logic BV)

; Finalize an MXINT8 addition by normalising the 5-bit raw sum and updating
; the 4-bit exponent. The output packs the 4-bit mantissa (MSBs) and the
; 4-bit exponent (LSBs): concat(mant, exp).

(synth-fun normalise_addition
    ((raw_sum (_ BitVec 5)) (target_exp (_ BitVec 4)))
    (_ BitVec 8)

    (
        (Start8    (_ BitVec 8))
        (FinalMant (_ BitVec 4))
        (FinalExp  (_ BitVec 4))
        (RawSumExt (_ BitVec 5))
        (AbsSum5   (_ BitVec 5))
        (ShiftAmt4 (_ BitVec 4))
        (Overflow  Bool)
    )

    (
      ; Pack mantissa || exponent
      (Start8 (_ BitVec 8) (
        (concat FinalMant FinalExp)
      ))

      ; Choices for the final mantissa
      (FinalMant (_ BitVec 4) (
        ((_ extract 3 0) raw_sum)
        ((_ extract 3 0) RawSumExt)
        ((_ extract 3 0) (bvashr RawSumExt #b00001))
        ((_ extract 3 0) (bvshl RawSumExt ((_ zero_extend 1) ShiftAmt4)))
        (ite Overflow
             ((_ extract 3 0) (bvashr RawSumExt #b00001))
             ((_ extract 3 0) (bvshl RawSumExt ((_ zero_extend 1) ShiftAmt4))))
      ))

      ; Choices for the final exponent
      (FinalExp (_ BitVec 4) (
        target_exp
        (bvadd target_exp #b0001)
        (bvsub target_exp #b0001)
        (bvsub target_exp ShiftAmt4)
        (ite Overflow
             (bvadd target_exp #b0001)
             (bvsub target_exp ShiftAmt4))
      ))

      ; Raw sum helpers
      (RawSumExt (_ BitVec 5) (
        raw_sum
        (bvneg raw_sum)
        (ite (bvslt raw_sum #b00000) (bvneg raw_sum) raw_sum)
      ))

      (AbsSum5 (_ BitVec 5) (
        (ite (bvslt raw_sum #b00000) (bvneg raw_sum) raw_sum)
      ))

      (ShiftAmt4 (_ BitVec 4) (
        #b0000 #b0001 #b0010 #b0011
        ((_ zero_extend 2) ((_ extract 3 2) AbsSum5))
      ))

      (Overflow Bool (
        (or (bvsgt RawSumExt #b00111) (bvslt RawSumExt #b11000))
      ))
    )
)

(declare-var raw_sum (_ BitVec 5))
(declare-var target_exp (_ BitVec 4))
