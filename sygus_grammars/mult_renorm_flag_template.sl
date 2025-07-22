(set-logic BV)

(synth-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1)

    (
        (Start1 (_ BitVec 1))
        (Condition Bool)
        (Product8 (_ BitVec 8))
        (Constant8 (_ BitVec 8))
    )

    (
      (Start1 (_ BitVec 1) (
        (ite Condition #b1 #b0)
      ))

      (Condition Bool (
        (bvsle Product8 Constant8)
        (bvslt Product8 Constant8)
      ))

      (Product8 (_ BitVec 8) (
        (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))
      ))
      
    
      (Constant8 (_ BitVec 8) (
          #x10  ; 16
          #x1F  ; 31
          #x20  ; 32 
          #x21  ; 33
          #x40  ; 64
      
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))

