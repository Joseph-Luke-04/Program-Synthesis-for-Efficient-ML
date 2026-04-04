(define-fun fp32_mult_raw48_carry ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 48)
  (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))

(define-fun fp32_mult_round_carry ((Ma (_ BitVec 24)) (Mb (_ BitVec 24)) (renorm (_ BitVec 1))) (_ BitVec 1) (let ((_let_1 (fp32_mult_raw48_carry Ma Mb))) (ite (and (= ((_ extract 22 22) _let_1) #b1) (= ((_ extract 46 23) _let_1) #b111111111111111111111111)) #b1 #b0)))