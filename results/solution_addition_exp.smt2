(
(define-fun add_mxint_exp ((m1 (_ BitVec 4)) (e1 (_ BitVec 4))
                                      (m2 (_ BitVec 4)) (e2 (_ BitVec 4)))
                                     (_ BitVec 4)
  (let ((target_exp (ite (bvsge e1 e2) e1 e2)))
  (let ((diff (ite (bvsge e1 e2) (bvsub e1 e2) (bvsub e2 e1))))
  (let ((aligned_m1 (ite (bvsge e1 e2) m1 (bvashr m1 diff))))
  (let ((aligned_m2 (ite (bvsge e1 e2) (bvashr m2 diff) m2)))
  (let ((sum5 (bvadd ((_ sign_extend 1) aligned_m1) ((_ sign_extend 1) aligned_m2))))
  (let ((overflow (or (bvsgt sum5 #b00111) (bvslt sum5 #b11000))))

    (ite overflow
         (bvadd target_exp #b0001)

         (let ((abs_sum (ite (bvslt sum5 #b00000) (bvneg sum5) sum5)))

           (let ((shift_amt (ite (bvslt abs_sum #b00100) 
                                 (ite (bvslt abs_sum #b00010) #b0010 #b0001)
                                 #b0000))) 
             (bvsub target_exp shift_amt)))
  )))))))
)
)
