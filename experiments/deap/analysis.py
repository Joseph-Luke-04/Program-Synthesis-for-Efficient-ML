import matplotlib.pyplot as plt
import numpy as np


from ground_truth import add_mxint_gt, dequantize_from_mxint
from add import synthesized_m_out

from ground_truth import MANTISSA_MIN, MANTISSA_MAX, EXPONENT_MIN_VAL, EXPONENT_MAX_VAL

def run_analysis(num_samples=1000):
   
    m1s = np.random.randint(MANTISSA_MIN, MANTISSA_MAX + 1, size=num_samples)
    e1s = np.random.randint(EXPONENT_MIN_VAL, EXPONENT_MAX_VAL + 1, size=num_samples)
    m2s = np.random.randint(MANTISSA_MIN, MANTISSA_MAX + 1, size=num_samples)
    e2s = np.random.randint(EXPONENT_MIN_VAL, EXPONENT_MAX_VAL + 1, size=num_samples)

    ground_truth_vals = []
    synthesized_vals = []
    errors = []

    for i in range(num_samples):
        m1, e1, m2, e2 = m1s[i], e1s[i], m2s[i], e2s[i]

    
        m_true, e_true = add_mxint_gt(m1, e1, m2, e2)
        
       
        m_synth = synthesized_m_out(m1, e1, m2, e2)

       
        val_true = dequantize_from_mxint(m_true, e_true)
        val_synth = dequantize_from_mxint(m_synth, e_true)

        ground_truth_vals.append(val_true)
        synthesized_vals.append(val_synth)
        errors.append(val_true - val_synth)

    return ground_truth_vals, synthesized_vals, errors


def plot_results(ground_truth, synthesized, errors):

    plt.figure(figsize=(10, 5))
    plt.subplot(1, 2, 1)
    
  
    perfect_line = [min(ground_truth), max(ground_truth)]
    plt.plot(perfect_line, perfect_line, 'r--', label='Perfect Prediction (y=x)')
    
    plt.scatter(ground_truth, synthesized, alpha=0.5, s=10)
    plt.title('Synthesized vs. Ground Truth Values')
    plt.xlabel('Ground Truth Float Value')
    plt.ylabel('Synthesized Float Value')
    plt.grid(True)
    plt.legend()
    plt.axis('equal') 


    plt.subplot(1, 2, 2)
    plt.hist(errors, bins=50)

    plt.xlabel('Error Value')
    plt.ylabel('Frequency')
    plt.grid(True)

    plt.tight_layout()
    
    plt.savefig("result")
    
    plt.close()

if __name__ == "__main__":
    truth_vals, synth_vals, error_vals = run_analysis()
    plot_results(truth_vals, synth_vals, error_vals)