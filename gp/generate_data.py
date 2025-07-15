import numpy as np
import random

from ground_truth import (
    add_mxint_gt,
    MANTISSA_MIN, MANTISSA_MAX,
    EXPONENT_MIN_VAL, EXPONENT_MAX_VAL
)

def generate_dataset(num_samples: int) -> list:
    dataset = []
    
    m1s = np.random.randint(MANTISSA_MIN, MANTISSA_MAX + 1, size=num_samples)
    e1s = np.random.randint(EXPONENT_MIN_VAL, EXPONENT_MAX_VAL + 1, size=num_samples)
    m2s = np.random.randint(MANTISSA_MIN, MANTISSA_MAX + 1, size=num_samples)
    e2s = np.random.randint(EXPONENT_MIN_VAL, EXPONENT_MAX_VAL + 1, size=num_samples)

    for i in range(num_samples):
        m1, e1, m2, e2 = m1s[i], e1s[i], m2s[i], e2s[i]
        
        m_out, e_out = add_mxint_gt(m1, e1, m2, e2)
        
        inputs = (int(m1), int(e1), int(m2), int(e2))
        outputs = (m_out, e_out)
        dataset.append((inputs, outputs))
    
    return dataset

DATASET = generate_dataset(1000)
