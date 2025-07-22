(set-logic BV)

(synth-fun mult_mxint_mant ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 4)

    (
        (Start4 (_ BitVec 4)) 

        (Intermediate8 (_ BitVec 8))
        (Condition Bool)
        (OriginalProduct8 (_ BitVec 8))
        (AbsProduct8 (_ BitVec 8))
    )

    (
      (Start4 (_ BitVec 4) (
        ((_ extract 3 0) Intermediate8)
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