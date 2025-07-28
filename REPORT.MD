
# Approximate Program Synthesis for Efficient Machine Learning

This doc contains more detailed information on the project and the experiments I ran, what worked and what didn't, and generally anything that's out of place in the [README.MD](README.MD).

# 1. Project Goal

## 1.1 Motivation
Modern machine learning accelerators rely heavily on low-precision number formats to improve computational and memory efficiency. While formats like **[MXInt](https://arxiv.org/pdf/2310.10537)** offer performance gains, the process of designing their underlying arithmetic is complex and time-consuming.

## 1.2. Automatic Discovery with SyGuS
This project investigates an alternative to manual design: using a **Syntax-Guided Synthesizer (SyGuS)** to automatically discover and generate the hardware logic for these operations. The primary goal was to investigate if a solver, given only a set of input-output constraints and a grammar of allowed operations, could successfully synthesize an (approximately) correct and efficient SMT-LIB representation of the target function.

For this investigation, I focused on the **MXInt** format, allocating **4 bits for the mantissa and 4 bits for the exponent**.

# 2. What Worked Well

## Synthesis Strategy
My strategy was centered on an **iterative synthesis loop**. Instead of giving the SyGuS solver all constraints at once, I guided it by adding them incrementally.

Once provided with a grammar, the solver starts with an initial set of constraints derived from randomly generated test cases. These constraints are added one by one to a growing list of accepted examples. After adding a new constraint, the solver attempts to find a function that satisfies the entire list. If the solver timed out or failed to find a solution with the new constraint, that constraint was discarded.

 I considered a synthesis run successful if the final program could satisfy a high percentage (e.g., >90%) of the constraints, making it a good approximation of the target function. I also used custom constraints to help guide the solver before introducing more complex random ones.

## 2.1. Multiplier
I started with the multiplication operation as it is the simplest. Attempting to synthesize the entire operation `f(m1, e1, m2, e2) -> (m_out, e_out)` in one go proved too difficult, as the solver struggled with the large search space and kept timing out. Synthesizing component-wise was a lot more effective.

My thought process for this decomposition was directly inspired by the standard hardware architecture for floating-point multipliers. I calculated the mantissa and exponent separately, starting with the latter. 

#### Mantissa and Renormalization Flag
I first synthesised a function that took two 4-bit mantissas and produced `renorm_flag`. This flag is asserted (`1`) if the product of the true mantissas is less than or equal to `0.5`, telling us that an exponent correction is needed. This part could have probably been synthethised by hand. The grammar used is in the file `sygus_grammars/multiplier_renorm_flag_template.sygus`, and the SyGuS output is in `results/solution_multiplication_renorm_flag.smt2`.

Next to synthethise the actual mantissa multiplication, I extended both mantissas to 8 bits, performed the multiplication, and had the synthesizer check for the renormalization flag and find the necessary mantissa shift. The grammar used is in `grammars/mult_mant_template.sygus`, and the SyGuS output is in `results/solution_multiplication_mant.smt2`.

#### Exponent
The exponent synthesis was more straightforward. The function SyGuS had to synthesize would take in the two 4-bit exponents and the renormalization flag. If the flag was 0, it would simply add the exponents. Otherwise, it found the correction constant. The grammar used is in `grammars/mult_exp_template.sygus`, and the SyGuS output is in `results/solution_multiplication_exp.smt2`.

#### Performance
I tested the synthesized multiplier on a set of 1000 random inputs, comparing the results to the ground truth. These results can be reproduced with the notebook `notebooks/evaluate.ipynb`. The results are summarized in the table below:



| Metric                | Mantissa | Exponent | Dequantized Value |
| :-------------------- | :------- | :------- | :---------------- |
| **Total Test Cases**    | 1000     | 1000     | 1000              |
| **Exact Matches**     | 95.20%   | 95.20%   | 98.60%            |
| **Mean Absolute Error** | 0.3040   | 0.048    | 0.776             |
| **Median Absolute Error** | 0.0      | 0.0      | 0.00              |
| **Max Absolute Error**  | 12       | 1        | 127.99 |


## 2.2. Adder

TODO! The results can be seen in `notebooks/evaluate.ipynb`. 

# 3. What Didn't Work Well (for me)

## 3.1 Synthesis challenge

Initially I attempted to synthesize the entire mantissa/exponent multiplication functions in one go. This would work for 2 or 3 constraints, but the solver would quickly time out afterwards.

I first attempted to mitigate this by loosening the constraints, allowing the solver to accept solutions that were in a certain range of the ground truth. The main issue with this approach was the SyGuS only allowed me to have an integer range, and a difference of 1 in the exponent is too signicant to be ignored. While this did prevent the solver from timing out, the functions it found were not useful. 

## 3.2 Genetic Programming
I also attempted a couple of experiments with genetic programming using the DEAP library, attempting to synthesize an addition function. The idea behind genetic programming is to evolve a population of candidate solutions over generations, selecting the fittest individuals based on their performance against a set of constraints. My fitness function was the mean absolute error of the candidate solution against a set of test cases. Unfortunately, I did not have much succes with this approach, though I did not spend much time on it. The (self-contained) code can be found in the `experiments/deap` directory.


# 4. Next Steps

### Dot Product
The most logical next goal would be to synthesize a satisfactory **dot product function**, since a dot product is the core of matrix multiplication. This introduces a new challenge: the MXInt data format shares the exponent across all elements in the vector.

