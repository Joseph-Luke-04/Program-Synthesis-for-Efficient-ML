(set-logic BV)

(synth-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1)


    (
        (Start1 (_ BitVec 1))
        (Condition Bool)
        (AbsProduct8 (_ BitVec 8))   
        (Constant8 (_ BitVec 8))      
    )

    
    (
      (Start1 (_ BitVec 1) (
        (ite Condition #b1 #b0)
      ))

      
      (Condition Bool (
        (bvsle AbsProduct8 Constant8)
      ))
      
      
      (AbsProduct8 (_ BitVec 8) (
        (let ((raw_product (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))))
          (ite (bvslt raw_product #x00) (bvneg raw_product) raw_product))
      ))
      
    
      (Constant8 (_ BitVec 8) (
          #x1F  ; 31 
          #x20  ; 32
          #x28  ; 40
          #x2A  ; 42
          (Constant (_ BitVec 8)) 
      ))
    )
)

(declare-var m1 (_ BitVec 4))
(declare-var m2 (_ BitVec 4))