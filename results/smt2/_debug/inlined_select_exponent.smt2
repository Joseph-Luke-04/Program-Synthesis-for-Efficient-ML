(define-fun select_exponent ((e1 (_ BitVec 4)) (e2 (_ BitVec 4))) (_ BitVec 4) (ite (bvsge e1 e2) e1 e2))
