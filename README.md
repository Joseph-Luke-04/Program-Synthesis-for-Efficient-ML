# Approximate Program Synthesis for Efficient Machine Learning

This repository contains the code and results for a summer research project on automatically generating hardware logic for operations in low-precision number formats used in machine learning.

This project was completed under the supervision of Dr. Jianyi Cheng and Dr. Elizabeth Polgreen.

We use Syntax-Guided Synthesis (SyGuS) to automatically discover hardware logic. The core of the project is an iterative loop that builds a solution by incrementally adding constraints:

## Reproducing the Results

**Prerequisites:**
*   Python 3.8+
*   [CVC5 SMT Solver](https://cvc5.github.io/)

**Instructions:**
1.  Clone the repository:
    ```bash
    git clone <https://github.com/misha7b/Program-Synthesis-for-Efficient-ML>
    cd <cd Program-Synthesis-for-Efficient-ML>
    ```

2.  Install the required Python packages:
    ```bash
    pip install -r requirements.txt
    ```
4.  **Run the Synthesis:**
    ```bash
    python src/synthesis.py
    ```