(set-logic BV)

(synth-fun mult_mxint_exp ((e1 (_ BitVec 4)) (e2 (_ BitVec 4)) (renorm_flag (_ BitVec 1))) (_ BitVec 4)

    (
        (Start4 (_ BitVec 4))
        (Correction_Const (_ BitVec 4)) 
    )

    (
      (Start4 (_ BitVec 4) (
        (ite (= renorm_flag #b1)
             (bvsub (bvadd e1 e2) Correction_Const) 
             (bvadd e1 e2)                          
        )
      ))
      
      (Correction_Const (_ BitVec 4) (
          #b0000  ; 0
          #b0001  ; 1 
          #b0010  ; 2
      ))
    )
)