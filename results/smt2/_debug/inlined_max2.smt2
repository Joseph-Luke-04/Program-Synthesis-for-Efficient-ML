(define-fun max2 ((x (_ BitVec 4)) (y (_ BitVec 4))) (_ BitVec 4) (ite (bvugt y x) y x))
