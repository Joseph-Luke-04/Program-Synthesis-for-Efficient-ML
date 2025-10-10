(
(define-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1) (let ((_let_1 (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2)))) (ite (bvsle (ite (bvslt _let_1 #b00000000) (bvneg _let_1) _let_1) #b00100000) #b1 #b0)))
)