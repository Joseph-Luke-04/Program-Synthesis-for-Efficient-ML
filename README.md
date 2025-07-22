# Approximate Program Synthesis for Efficient Machine Learning

This repository contains the code and results for a summer research project on automatically generating hardware logic for operations in low-precision number formats used in machine learning.

This project was completed under the supervision of Dr. Jianyi Cheng and Dr. Elizabeth Polgreen.

We use Syntax-Guided Synthesis (SyGuS) to automatically discover hardware logic. The core of the project is an iterative loop that builds a solution by incrementally adding constraints:

## Reproducing the Results

**Prerequisites:**
*   Python 3.8+
*   [CVC5 SMT Solver](https://cvc5.github.io/): Ensure the `cvc5` executable is installed and available in your system's PATH.

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

    All synthesis runs are controlled from the main driver script.

    a. **Open `src/synthesis_driver.py`** and go to the `if __name__ == "__main__":` block at the bottom.

    b. **Edit the configuration** to choose which operation and component you want to synthesize. For example, to synthesize the multiplication `renorm_flag`:
    ```python
    # In src/synthesis_driver.py

    # Step 1: Choose the Operation
    target_operation = MultiplicationTarget()

    # Step 2: Choose the Component
    target_component = "renorm_flag"
    ```

    c. **Execute the driver** from the project's main directory:
    ```bash
    python -m src.synthesis_driver
    ```
    The results will be saved in the `results/` folder.