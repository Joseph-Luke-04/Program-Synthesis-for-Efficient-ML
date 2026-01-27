(sygus-enum (concat (mult_mxint_mant m1 m2) (mult_mxint_exp e1 e2 (mult_renorm_flag m1 m2))))
(sygus-candidate (mult_mxint_full_product (concat (mult_mxint_mant m1 m2) (mult_mxint_exp e1 e2 (mult_renorm_flag m1 m2)))))
(
(define-fun mult_mxint_full_product ((m1 (_ BitVec 4)) (e1 (_ BitVec 4)) (m2 (_ BitVec 4)) (e2 (_ BitVec 4)) (renorm_flag (_ BitVec 1))) (_ BitVec 8) (concat (mult_mxint_mant m1 m2) (mult_mxint_exp e1 e2 (mult_renorm_flag m1 m2))))
)