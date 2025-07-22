# Approximate Program Synthesis for Efficient Machine Learning

This doc contains more detailed information on the project and the experiments I ran, what worked and what didn't, and generally anything that's out of place in the [README.MD](README.MD).

---
## 1.1 Motivation
Modern machine learning accelerators rely heavily on low-precision number formats to improve computational and memory efficiency. While formats like **[MXInt](https://arxiv.org/pdf/2310.10537)** offer performance gains, the process of designing their underlying arithmetic is complex and time-consuming.

## 1.2. Automatic Discovery with SyGuS
This project investigates an alternative to manual design: using a **Syntax-Guided Synthesizer (SyGuS)** to automatically discover and generate the hardware logic for these operations. The primary goal was to determine if a solver, given only a set of input-output constraints and a grammar of allowed operations, could successfully synthesize an (approximately) correct and efficient SMT-LIB representation of the target function.

For this investigation, we focused on a custom **MXInt4** variant, allocating **4 bits for the mantissa and 4 bits for the exponent**.
