(sygus-enum (let ((_let_1 (add_raw m1 e1 m2 e2))) (normalise_addition ((_ extract 8 4) _let_1) ((_ extract 3 0) _let_1))))
(sygus-candidate (add_full_sum (let ((_let_1 (add_raw m1 e1 m2 e2))) (normalise_addition ((_ extract 8 4) _let_1) ((_ extract 3 0) _let_1)))))
(
(define-fun add_full_sum ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 8) (let ((_let_1 (add_raw m1 e1 m2 e2))) (normalise_addition ((_ extract 8 4) _let_1) ((_ extract 3 0) _let_1))))
)