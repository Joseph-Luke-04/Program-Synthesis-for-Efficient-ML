"""
Best program found:
sub(max(rshift(sub(ARG3, 2), max(ARG0, ARG1)), max(rshift(sub(ARG0, 2), ARG2),
min(rshift(ARG0, max(max(ARG2, add(ARG3, ARG3)), mul(rshift(ARG1, 2), ARG2))), ARG0))),
sub(max(min(ARG0, mul(ARG0, rshift(sub(ARG3, max(max(ARG1, ARG3), mul(ARG3, ARG3))), -1))),
rshift(ARG2, ARG2)), ARG2))
Fitness (MSE): 0.275
"""

def rshift(val, bits):
    bits = max(0, int(round(abs(bits))))
    return val >> bits

def add(a, b): return a + b
def sub(a, b): return a - b
def mul(a, b): return a * b

def synthesized_m_out(m1, e1, m2, e2):
   
    ARG0 = m1
    ARG1 = e1
    ARG2 = m2
    ARG3 = e2
    
    term1 = max(rshift(sub(ARG3, 2), max(ARG0, ARG1)), max(rshift(sub(ARG0, 2), ARG2), min(rshift(ARG0, max(max(ARG2, add(ARG3, ARG3)), mul(rshift(ARG1, 2), ARG2))), ARG0)))
    term2 = sub(max(min(ARG0, mul(ARG0, rshift(sub(ARG3, max(max(ARG1, ARG3), mul(ARG3, ARG3))), -1))), rshift(ARG2, ARG2)), ARG2)
    
    return sub(term1, term2)