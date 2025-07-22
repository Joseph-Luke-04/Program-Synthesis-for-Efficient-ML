(set-logic BV)

(synth-fun mult_mxint_mant_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 5)

    (
        (Start5 (_ BitVec 5))
        (FinalMant4 (_ BitVec 4))
        (FinalFlag1 (_ BitVec 1))
        (Intermediate8 (_ BitVec 8))
        (Condition Bool)
        (OriginalProduct8 (_ BitVec 8))
        (AbsProduct8 (_ BitVec 8))
    )

    (
      (Start5 (_ BitVec 5) (
        (concat FinalMant4 FinalFlag1)
      ))

      (FinalMant4 (_ BitVec 4) (
        ((_ extract 3 0) Intermediate8)
      ))

      (FinalFlag1 (_ BitVec 1) (
        (ite Condition #b1 #b0)
      ))

      (Intermediate8 (_ BitVec 8) (
        (ite Condition
             (bvashr (bvshl OriginalProduct8 #x01) #x03)
             (bvashr OriginalProduct8 #x03)
        )
      ))

      (Condition Bool (
        (bvsle AbsProduct8 #x20)
      ))

      (OriginalProduct8 (_ BitVec 8) (
        (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
      ))
      
      (AbsProduct8 (_ BitVec 8) (
        (ite (bvslt OriginalProduct8 #x00)
             (bvneg OriginalProduct8)
             OriginalProduct8)
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))