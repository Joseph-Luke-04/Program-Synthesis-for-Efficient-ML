import operator
import math
import random
import numpy as np

from deap import algorithms, base, creator, tools, gp

from ground_truth import dequantize_from_mxint

from generate_data import DATASET
from ground_truth import MANTISSA_MAX, MANTISSA_MIN


class Mantissa(int): pass
class Exponent(int): pass

class MyBool(int): pass



pset = gp.PrimitiveSetTyped("MAIN", [Mantissa, Exponent, Mantissa, Exponent], Mantissa)


pset.addPrimitive(operator.add, [Mantissa, Mantissa], Mantissa, name="add_m")
pset.addPrimitive(operator.sub, [Mantissa, Mantissa], Mantissa, name="sub_m")
pset.addPrimitive(max, [Exponent, Exponent], Exponent, name="max_e")
pset.addPrimitive(operator.sub, [Exponent, Exponent], Exponent, name="sub_e")
def safe_right_shift(val: Mantissa, bits: Exponent) -> Mantissa:
    bits = max(0, int(round(abs(bits))))
    return val >> bits
pset.addPrimitive(safe_right_shift, [Mantissa, Exponent], Mantissa, name="rshift_m_by_e")



def is_greater_than(a: Mantissa, b: Mantissa) -> MyBool:
    return MyBool(a > b)
pset.addPrimitive(is_greater_than, [Mantissa, Mantissa], MyBool, name="is_gt_m")


def if_then_else(condition: MyBool, out1: Mantissa, out2: Mantissa) -> Mantissa:
    return out1 if condition else out2
pset.addPrimitive(if_then_else, [MyBool, Mantissa, Mantissa], Mantissa, name="if_m")


pset.addTerminal(0, Mantissa, name="m_const_0")
pset.addTerminal(1, Mantissa, name="m_const_1")
pset.addTerminal(0, Exponent, name="e_const_0")
pset.addTerminal(1, Exponent, name="e_const_1")

pset.addTerminal(MANTISSA_MAX, Mantissa, "MANTISSA_MAX")

pset.addTerminal(MyBool(True), MyBool, name="TRUE")
pset.addTerminal(MyBool(False), MyBool, name="FALSE")


creator.create("FitnessMin", base.Fitness, weights=(-1.0,))
creator.create("Individual", gp.PrimitiveTree, fitness=creator.FitnessMin, pset=pset)
toolbox = base.Toolbox()
toolbox.register("expr", gp.genHalfAndHalf, pset=pset, min_=1, max_=6) # Allow slightly deeper trees for if/else
toolbox.register("individual", tools.initIterate, creator.Individual, toolbox.expr)
toolbox.register("population", tools.initRepeat, list, toolbox.individual)
toolbox.register("compile", gp.compile, pset=pset)

def eval_program(individual):
    program = toolbox.compile(expr=individual)
    
    errors = []
    
    for inputs, expected_outputs in DATASET:
        m_out_expected, e_out_expected = expected_outputs
        
        try:
            m_out_predicted = program(*inputs)
          
            val_true = dequantize_from_mxint(m_out_expected, e_out_expected)
            val_predicted = dequantize_from_mxint(m_out_predicted, e_out_expected)

            absolute_error = abs(val_predicted - val_true)
            errors.append(absolute_error)

        except (ValueError, OverflowError, ZeroDivisionError, TypeError):
            return float('inf'),


    if not errors:
        return float('inf'),

    fitness_value = np.percentile(errors, 98)
    
    return fitness_value,

toolbox.register("evaluate", eval_program)
toolbox.register("select", tools.selTournament, tournsize=3)
toolbox.register("mate", gp.cxOnePoint)
toolbox.register("expr_mut", gp.genFull, min_=0, max_=2)
toolbox.register("mutate", gp.mutUniform, expr=toolbox.expr_mut, pset=pset)
toolbox.decorate("mate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17))
toolbox.decorate("mutate", gp.staticLimit(key=operator.attrgetter("height"), max_value=17))


if __name__ == "__main__":
    random.seed(42)
    pop = toolbox.population(n=500)
    hof = tools.HallOfFame(1)
    stats_fit = tools.Statistics(lambda ind: ind.fitness.values)
    mstats = tools.MultiStatistics(fitness=stats_fit)
    mstats.register("min", np.min)
    
    
    algorithms.eaSimple(pop, toolbox, 0.7, 0.2, 150, # More generations
                        stats=mstats, halloffame=hof, verbose=True)

    print("\n--- Synthesis Complete ---")
    print("Best program found:")
    print(str(hof[0]))
    print(f"Fitness: {hof[0].fitness.values[0]}")