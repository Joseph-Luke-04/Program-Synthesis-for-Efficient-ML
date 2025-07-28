# Approximate Program Synthesis for Efficient Machine Learning

This repository contains the code and results for a summer research project on automatically generating hardware logic for operations in low-precision number formats used in machine learning.

We use Syntax-Guided Synthesis (SyGuS) to automatically discover hardware logic. The core of the project is an iterative loop that builds a solution by incrementally adding constraints. For more specific details of my results and experiments, check out [REPORT.MD](REPORT.MD).

This project was completed under the supervision of Dr. Jianyi Cheng and Dr. Elizabeth Polgreen.

## Reproducing the Results

**Prerequisites:**
*   Python 3.8+
*   [CVC5 SMT Solver](https://cvc5.github.io/) (Version 1.2.2-dev.335.a5f64f218)

**Instructions:**

1.  **Clone the Repository**
    ```bash
    git clone https://github.com/misha7b/Program-Synthesis-for-Efficient-ML
    cd Program-Synthesis-for-Efficient-ML
    ```

2.  **Install Dependencies**
    ```bash
    pip install -r requirements.txt
    ```

3.  **Configure and Run Synthesis**

    a. **Open `src/synthesis_driver.py`** and go to the `if __name__ == "__main__":` block at the bottom.

    b. **Edit the configuration** to choose which operation and component you want to synthesize. The available targets are:

    *   **For `MultiplicationTarget()`**:
        *   `"mant"`: Synthesizes the 4-bit mantissa logic.
        *   `"exp"`: Synthesizes the 4-bit exponent logic.
        *   `"renorm_flag"`: Synthesizes the 1-bit renormalization flag.

    *   **For `AdditionTarget()`**:
        *   `"alignment"`: Synthesizes the logic to select the target exponent and shift the mantissas accordingly.
        *   `"raw_sum"`: Synthesizes the logic to add the two aligned mantissas into a wider (5-bit) sum.
        *   `"overflow"`: Synthesizes the logic to detect if the **raw_sum** is outside the representable range of the final format.

    Below is an example configuration for synthesizing the **exponent** logic for **multiplication**:
    ```python
    # In src/synthesis_driver.py

    # --- Step 1: Choose the Operation ---
    # Options: MultiplicationTarget(), AdditionTarget()
    target_operation = MultiplicationTarget()

    # --- Step 2: Choose the Component ---
    # For Multiplication: "mant", "exp", "renorm_flag"
    # For Addition: " "alignment", "raw_sum", "overflow"
    target_component = "exp"
    ```

    c. **Execute the Synthesis Driver**

    From the project's main directory, run:
    
    ```bash
    python -m src.synthesis_driver
    ```
    
    This will start the synthesis process.
    
    ### Example output:
    
    ```bash
    python -m src.synthesis_driver
    --- Starting Synthesis for [MultiplicationTarget -> renorm_flag] ---
    
    --- Iteration 1/30 ---
    Generating new constraint with inputs: (-2.790110127032232, 6.220312281964439)
    (constraint (= (mult_renorm_flag #b1010 #b0110) #b0))
    SUCCESS: Constraint accepted. Total constraints: 1
    
    ...
    
    --- Iteration 30/30 ---
    Generating new constraint with inputs: (3.418870565422649, -10.004808356462656)
    (constraint (= (mult_renorm_flag #b0110 #b1010) #b0))
    SUCCESS: Constraint accepted. Total constraints: 30
    
    --- Synthesis Complete! ---
    
    Constraints accepted: 30/30
    
    --- Final Synthesized Program ---
    (
    (define-fun mult_renorm_flag ((m1 (_ BitVec 4)) (m2 (_ BitVec 4))) (_ BitVec 1)
      (let ((_let_1 (bvmul ((_ sign_extend 4) m1) ((_ sign_extend 4) m2))))
        (ite (bvsle
               (ite (bvslt _let_1 #b00000000)
                    (bvneg _let_1)
                    _let_1)
               #b00011111)
             #b1
             #b0)))
    )
    ```
