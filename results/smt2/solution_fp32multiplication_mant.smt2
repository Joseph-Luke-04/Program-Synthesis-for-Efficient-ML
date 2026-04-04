(define-fun fp32_mult_raw48 ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(define-fun fp32_mult_mant ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)) (renorm (_ BitVec 1))) (_ BitVec 23) (let ((_let_1 (bvlshr (fp32_mult_raw48 Ma Mb) ((_ zero_extend 47) renorm)))) ((_ extract 22 0) (bvadd ((_ extract 46 23) _let_1) ((_ zero_extend 23) ((_ extract 22 22) _let_1))))))