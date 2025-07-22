# Approximate Program Synthesis for Efficient Machine Learning

This repository contains the code and results for a summer research project on automatically generating hardware logic for operations in low-precision number formats used in machine learning.

This project was completed under the supervision of Dr. Jianyi Cheng and Dr. Elizabeth Polgreen.

We use Syntax-Guided Synthesis (SyGuS) to automatically discover hardware logic. The core of the project is an iterative loop that builds a solution by incrementally adding constraints. For more specific details of my results and experiments, check out *REPORT.MD*.

## Reproducing the Results

**Prerequisites:**
*   Python 3.8+
*   [CVC5 SMT Solver](https://cvc5.github.io/)

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
        *   *TODO:*

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

    c. **Execute the driver** from the project's main directory:
    ```bash
    python -m src.synthesis_driver
    ```
    The results will be printed in the terminal and saved in the `results/` folder.
