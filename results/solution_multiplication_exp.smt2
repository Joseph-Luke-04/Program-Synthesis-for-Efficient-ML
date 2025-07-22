(
(define-fun mult_mxint_exp ((e1 (_ BitVec 4)) (e2 (_ BitVec 4)) (renorm_flag (_ BitVec 1))) (_ BitVec 4) (let ((_let_1 (bvadd e1 e2))) (ite (= renorm_flag #b1) (bvsub _let_1 #b0001) _let_1)))
)