(set-logic BV)

(synth-fun mult_mxint_full_product
  ((m1 (_ BitVec 4)) (e1 (_ BitVec 4))
   (m2 (_ BitVec 4)) (e2 (_ BitVec 4))
   (renorm_flag (_ BitVec 1)))
  (_ BitVec 8)

  (
    (Start8 (_ BitVec 8))
    (Mant4  (_ BitVec 4))
    (Exp4   (_ BitVec 4))
    (Flag1  (_ BitVec 1))
  )

  (
    ; pack as [mant(4)][exp(4)] to match your concatenated_result
    (Start8 (_ BitVec 8) (
      (concat Mant4 Exp4)
    ))

    (Mant4 (_ BitVec 4) (
      (mult_mxint_mant m1 m2)
    ))

    (Exp4 (_ BitVec 4) (
      (mult_mxint_exp e1 e2 Flag1)
    ))

    ; allow using passed-in renorm_flag OR recomputing it
    ; (recomputing is useful if later you remove renorm_flag from the interface)
    (Flag1 (_ BitVec 1) (
      renorm_flag
      (mult_renorm_flag m1 m2)
    ))
  )
)
