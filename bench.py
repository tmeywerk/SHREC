import warnings
with warnings.catch_warnings():
    warnings.filterwarnings("ignore",category=DeprecationWarning)
    import problem
from searcher import search_cnf, search_clause, search_lit
import generator
import pysmt.shortcuts as smt
import random

import time
import argparse
from timeout import timeout
from os.path import basename
from incremental_learner import AllViolationsStrategy
from smt_print import pretty_print

def main(filename, sample_count, seed):
    random.seed(seed)

    target_formula = smt.read_smtlib(filename)

    variables = target_formula.get_free_variables()
    var_names = [str(v) for v in variables]
    var_types = {str(v): v.symbol_type() for v in variables}
    var_domains = {str(v): (0, 1) for v in variables}  #FIXME: This is a hack. Adjust depending on your benchmarks

    domain = problem.Domain(var_names, var_types, var_domains)
    name = basename(filename).split(".")[0]
    target_problem = problem.Problem(domain, target_formula, name)

    samples = generator.get_problem_samples(target_problem, sample_count, 1)
    test_samples = generator.get_problem_samples(target_problem, 1000, 1)
    
    kwargs={"problem":target_problem, "data":samples}
    t1 = time.time()
    res1 = timeout(search_cnf, kwargs=kwargs, duration=600)
    t2 = time.time()
    res2 = timeout(search_clause, kwargs=kwargs, duration=600)
    t3 = time.time()
    res3 = timeout(search_lit, kwargs=kwargs, duration=600)
    t4 = time.time()

    dur1 = "TO" if res1 is None else t2 - t1
    dur2 = "TO" if res2 is None else t3 - t2
    dur3 = "TO" if res3 is None else t4 - t3

    formula1 = "None" if res1 is None else pretty_print(res1)
    formula2 = "None" if res2 is None else pretty_print(res2)
    formula3 = "None" if res3 is None else pretty_print(res3)

    #FIXME: this will show 1 for timeouts
    cl1 = formula1.count("&") + 1
    cl2 = formula2.count("&") + 1
    cl3 = formula3.count("&") + 1

    hl1 = formula1.count("<")
    hl2 = formula2.count("<")
    hl3 = formula3.count("<")

    strat = AllViolationsStrategy()

    train_acc1 = "N/A" if res1 is None else (1000 - len(list(strat.select_active(domain, samples, res1, [])))) / 1000
    train_acc2 = "N/A" if res2 is None else (1000 - len(list(strat.select_active(domain, samples, res2, [])))) / 1000
    train_acc3 = "N/A" if res3 is None else (1000 - len(list(strat.select_active(domain, samples, res3, [])))) / 1000
    
    acc1 = "N/A" if res1 is None else (1000 - len(list(strat.select_active(domain, test_samples, res1, [])))) / 1000
    acc2 = "N/A" if res2 is None else (1000 - len(list(strat.select_active(domain, test_samples, res2, [])))) / 1000
    acc3 = "N/A" if res3 is None else (1000 - len(list(strat.select_active(domain, test_samples, res3, [])))) / 1000

    print("[")
    print("file = {}".format(filename))
    print("samples= {}".format(sample_count))
    print("INCAL_result = {}".format(formula1))
    print("SHREC1_result = {}".format(formula2))
    print("SHREC2_result = {}".format(formula3))
    print("INCAL_time = {}".format(dur1))
    print("SHREC1_time = {}".format(dur2))
    print("SHREC2_time = {}".format(dur3))
    print("INCAL_clauses = {}".format(cl1))
    print("SHREC1_clauses = {}".format(cl2))
    print("SHREC2_clauses = {}".format(cl3))
    print("INCAL_halflines = {}".format(hl1))
    print("SHREC1_halflines = {}".format(hl2))
    print("SHREC2_halflines = {}".format(hl3))
    print("INCAL_cost = {}".format(cl1 + hl1))
    print("SHREC1_cost = {}".format(cl2 + hl2))
    print("SHREC2_cost = {}".format(cl3 + hl3))
    print("INCAL_train_acc = {}".format(train_acc1))
    print("SHREC1_train_acc = {}".format(train_acc2))
    print("SHREC2_train_acc = {}".format(train_acc3))
    print("INCAL_acc = {}".format(acc1))
    print("SHREC1_acc = {}".format(acc2))
    print("SHREC2_acc = {}".format(acc3))
    print("]")

if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("filename")
    parser.add_argument("sample_count", type=int)
    parser.add_argument("seed", type=int)
    args = parser.parse_args()
    main(args.filename, args.sample_count, args.seed)
