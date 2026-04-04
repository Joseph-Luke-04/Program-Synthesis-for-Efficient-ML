(define-fun fp32_mult_raw48_renorm ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(define-fun fp32_mult_renorm ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 1) ((_ extract 47 47) (fp32_mult_raw48_renorm Ma Mb)))