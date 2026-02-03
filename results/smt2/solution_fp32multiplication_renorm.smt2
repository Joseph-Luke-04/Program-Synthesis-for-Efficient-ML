(sygus-enum #b0 ((_ extract 45 45) (bvlshr (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)) #b000000000000000000000000000000000000000000000001)))
(sygus-enum #b1 ((_ extract 47 47) (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))))
(sygus-candidate (fp32_mult_renorm ((_ extract 47 47) (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb)))))
(
(define-fun fp32_mult_renorm ((Ma (_ BitVec 24)) (Mb (_ BitVec 24))) (_ BitVec 1) ((_ extract 47 47) (bvmul ((_ zero_extend 24) Ma) ((_ zero_extend 24) Mb))))
)