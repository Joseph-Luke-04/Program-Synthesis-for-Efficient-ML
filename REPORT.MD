
# Approximate Program Synthesis for Efficient Machine Learning

This doc contains more detailed information on the project and the experiments I ran, what worked and what didn't, and generally anything that's out of place in the [README.MD](README.MD).

# 1. Project Goal

## 1.1 Motivation
Modern machine learning accelerators rely heavily on low-precision number formats to improve computational and memory efficiency. While formats like **[MXInt](https://arxiv.org/pdf/2310.10537)** offer performance gains, the process of designing their underlying arithmetic is complex and time-consuming.

## 1.2. Automatic Discovery with SyGuS
This project investigates an alternative to manual design: using a **Syntax-Guided Synthesizer (SyGuS)** to automatically discover and generate the hardware logic for these operations. The primary goal was to investigate if a solver, given only a set of input-output constraints and a grammar of allowed operations, could successfully synthesize an (approximately) correct and efficient SMT-LIB representation of the target function.

For this investigation, I focused on the **MXInt** format, allocating **4 bits for the mantissa and 4 bits for the exponent**.

# 2. What Worked Well

## 2.1. Multiplier
I started with the multiplication operation as it is the simplest. Attempting to synthesize the entire operation `f(m1, e1, m2, e2) -> (m_out, e_out)` in one go proved too difficult, as the solver struggled with the large search space and kept timing out. Synthesizing component-wise was a lot more effective.

#### Mantissa and Renormalization Flag
I first synthesised a function that took two 4-bit mantissas and produced `renorm_flag`. This flag is asserted (`1`) if the product of the true mantissas is less than or equal to `0.5`, telling us that an exponent correction is needed.

## 2.2. Adder
