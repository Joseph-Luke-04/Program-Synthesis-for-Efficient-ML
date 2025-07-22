(
(define-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1) (ite (bvsle (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2)) #b00011111) #b1 #b0))
)