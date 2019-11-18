import pysmt.shortcuts as smt
import random
from incremental_learner import RandomViolationsStrategy
from pysmt.typing import REAL

DELTA = 0.0000000000001 #this avoids rounding errors in the halfspace coeficients

def find_iter(data, domain, idx, finder, *finder_args):
    strat = RandomViolationsStrategy(10)
    excluded = [i for i in range(len(data)) if i not in idx]
    active_indices = random.sample(idx, min(20, len(idx)))
    excluded += active_indices
    result = smt.TRUE() #will be replaced
    while len(active_indices) > 0 and result is not None:
        result = finder(data, domain, active_indices, *finder_args)
        if result is None:
            break
        active_indices = list(strat.select_active(domain, data, result, excluded))
        excluded += active_indices
    return result

def find_cnf(data, domain, active_indices, solver, n_c, n_h):
    # Constants
    n_b_original = len(domain.bool_vars)
    n_b = n_b_original * 2
    n_r = len(domain.real_vars)
    n_d = len(data)

    real_features = [[row[v] for v in domain.real_vars] for row, _ in data]
    bool_features = [[row[v] for v in domain.bool_vars] for row, _ in data]
    labels = [row[1] for row in data]

    # Variables
    a_hr = [[smt.Symbol("a_hr[{}][{}]".format(h, r), REAL) for r in range(n_r)] for h in range(n_h)]
    b_h = [smt.Symbol("b_h[{}]".format(h), REAL) for h in range(n_h)]
    s_ch = [[smt.Symbol("s_ch[{}][{}]".format(c, h)) for h in range(n_h)] for c in range(n_c)]
    s_cb = [[smt.Symbol("s_cb[{}][{}]".format(c, b)) for b in range(n_b)] for c in range(n_c)]

    # Aux variables
    s_ih = [[smt.Symbol("s_ih[{}][{}]".format(i, h)) for h in range(n_h)] for i in range(n_d)]
    s_ic = [[smt.Symbol("s_ic[{}][{}]".format(i, c)) for c in range(n_c)] for i in range(n_d)]

    # Constraints
    for i in active_indices:
        x_r, x_b, label = real_features[i], bool_features[i], labels[i]

        for h in range(n_h):
            sum_coefficients = smt.Plus([a_hr[h][r] * smt.Real(x_r[r]) for r in range(n_r)])
            if label:
                solver.add_assertion(smt.Iff(s_ih[i][h], sum_coefficients + DELTA <= b_h[h]))
            else:
                solver.add_assertion(smt.Iff(s_ih[i][h], sum_coefficients - DELTA <= b_h[h]))

        for c in range(n_c):
            solver.add_assertion(smt.Iff(s_ic[i][c], smt.Or(
                [smt.FALSE()]
                + [(s_ch[c][h] & s_ih[i][h]) for h in range(n_h)]
                + [s_cb[c][b] for b in range(n_b_original) if x_b[b]]
                + [s_cb[c][b] for b in range(n_b_original, n_b) if not x_b[b - n_b_original]]
            )))

        if label:
            solver.add_assertion(smt.And([s_ic[i][c] for c in range(n_c)]))
        else:
            solver.add_assertion(smt.Or([~s_ic[i][c] for c in range(n_c)]))

    if not solver.solve():
        return None
    model = solver.get_model()

    x_vars = [domain.get_symbol(domain.real_vars[r]) for r in range(n_r)]
    half_spaces = [
        smt.Plus([model.get_value(a_hr[h][r]) * x_vars[r] for r in range(n_r)]) <= model.get_value(b_h[h])
        for h in range(n_h)
    ]

    b_vars = [domain.get_symbol(domain.bool_vars[b]) for b in range(n_b_original)]
    bool_literals = [b_vars[b] for b in range(n_b_original)]
    bool_literals += [~b_vars[b] for b in range(n_b - n_b_original)]

    conjunctions = [
        [half_spaces[h] for h in range(n_h) if model.get_py_value(s_ch[c][h])]
        + [bool_literals[b] for b in range(n_b) if model.get_py_value(s_cb[c][b])]
        for c in range(n_c)
    ]

    return smt.And([smt.Or(conjunction) for conjunction in conjunctions])

def find_clause(data, domain, active_indices, solver, n_h):
    # Constants
    n_b_original = len(domain.bool_vars)
    n_b = n_b_original * 2
    n_r = len(domain.real_vars)
    n_d = len(data)

    real_features = [[row[v] for v in domain.real_vars] for row, _ in data]
    bool_features = [[row[v] for v in domain.bool_vars] for row, _ in data]
    labels = [row[1] for row in data]

    # Variables
    a_hr = [[smt.Symbol("a_hr[{}][{}]".format(h, r), REAL) for r in range(n_r)] for h in range(n_h)]
    b_h = [smt.Symbol("b_h[{}]".format(h), REAL) for h in range(n_h)]
    s_b = [smt.Symbol("s_b[{}]".format(b)) for b in range(n_b)]
    

    # Aux variables
    s_ih = [[smt.Symbol("s_ih[{}][{}]".format(i, h)) for h in range(n_h)] for i in range(n_d)]

    # Constraints
    for i in active_indices:
        x_r, x_b, label = real_features[i], bool_features[i], labels[i]

        for h in range(n_h):
            sum_coefficients = smt.Plus([a_hr[h][r] * smt.Real(x_r[r]) for r in range(n_r)])
            if label:
                solver.add_assertion(smt.Iff(s_ih[i][h], sum_coefficients + DELTA <= b_h[h]))
            else:
                solver.add_assertion(smt.Iff(s_ih[i][h], sum_coefficients - DELTA <= b_h[h]))
                


        if label:
            solver.add_assertion(smt.Or(
                [smt.FALSE()]
                + [s_ih[i][h] for h in range(n_h)]
                + [s_b[b] for b in range(n_b_original) if x_b[b]]
                + [s_b[b] for b in range(n_b_original, n_b) if not x_b[b - n_b_original]]
            ))
        else:
            solver.add_assertion(smt.And(
                [smt.TRUE()]
                + [~s_ih[i][h] for h in range(n_h)]
                + [~s_b[b] for b in range(n_b_original) if x_b[b]]
                + [~s_b[b] for b in range(n_b_original, n_b) if not x_b[b - n_b_original]]
            ))
            

    if not solver.solve():
        return None
    model = solver.get_model()

    x_vars = [domain.get_symbol(domain.real_vars[r]) for r in range(n_r)]
    half_spaces = [
        smt.Plus([model.get_value(a_hr[h][r]) * x_vars[r] for r in range(n_r)]) <= model.get_value(b_h[h])
        for h in range(n_h)
    ]

    b_vars = [domain.get_symbol(domain.bool_vars[b]) for b in range(n_b_original)]
    bool_literals = [b_vars[b] for b in range(n_b_original)]
    bool_literals += [~b_vars[b] for b in range(n_b - n_b_original)]

    return smt.Or(
        [half_spaces[h] for h in range(n_h)]
        + [bool_literals[b] for b in range(n_b) if model.get_py_value(s_b[b])]
    )

def find_hl(data, domain, active_indices, solver):
        
    # Constants
    n_r = len(domain.real_vars)

    real_features = [[row[v] for v in domain.real_vars] for row, _ in data]
    labels = [row[1] for row in data]

    # Variables
    a_r = [smt.Symbol("a_r[{}]".format(r), REAL) for r in range(n_r)]
    b = smt.Symbol("b", REAL)

    # Constraints
    for i in active_indices:
        x_r, label = real_features[i], labels[i]
        sum_coefficients = smt.Plus([a_r[r] * smt.Real(x_r[r]) for r in range(n_r)])
        if label:
            solver.add_assertion(sum_coefficients + DELTA <= b)
        else:
            solver.add_assertion(sum_coefficients - DELTA > b)

    if not solver.solve():
        return None
    model = solver.get_model()

    x_vars = [domain.get_symbol(domain.real_vars[r]) for r in range(n_r)]
    return smt.Plus([model.get_value(a_r[r]) * x_vars[r] for r in range(n_r)]) <= model.get_value(b)
    
