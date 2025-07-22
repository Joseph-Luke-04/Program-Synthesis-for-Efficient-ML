(
(define-fun add_raw ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 9) (let ((_let_1 (align_mantissas m1 e1 m2 e2))) (concat (bvadd ((_ sign_extend 1) ((_ extract 7 4) _let_1)) ((_ sign_extend 1) ((_ extract 3 0) _let_1))) (select_exponent e1 e2))))
)