from encoder import find_iter, find_cnf, find_clause, find_hl
from hierarchy_node import HierarchyNode, build_hierarchy
from queue import PriorityQueue
import pysmt.shortcuts as smt
from incremental_learner import SelectionStrategy
from collections import deque

##INCAL
def search_cnf(data, problem):
    domain = problem.domain
    cost = 1
    idx = range(len(data))
    while True:
        for clauses in range(1, cost):
            with smt.Solver() as solver:
                solution = find_iter(data, domain, idx, find_cnf, solver, clauses, cost - clauses)
                if solution is not None:
                    return solution
        cost += 1

##HIERARCHICAL LVL 1
def search_clause(data, problem):
    domain = problem.domain
    neg_idx = [i for i in range(len(data)) if not data[i][1]]
    hierarchy_root = build_hierarchy(data, domain, neg_idx)
    cost = 1
    while True:
        q = PriorityQueue()
        q.put(hierarchy_root)
        for clauses in range(1, cost):
            solution = search_in_hierarchy(data, domain, list(q.queue), cost - clauses)
            if solution is not None:
                return solution
            node = q.get()
            br = False
            while node.left is None or (node.hl_max is not None and node.hl_max <= (node.left.hl_min + node.right.hl_min + 1)):
                if node.prio() == float("inf"):
                    br = True
                    break;
                node.priority = None
                q.put(node)
                node = q.get()
            if br:
                break
            if node.left is not None:
                q.put(node.left)
                q.put(node.right)
        cost += 1


def search_in_hierarchy(data, domain, nodes, halflines):
    clauses = []
    for node in nodes:
        if node.hl_min == node.hl_max:
            clauses += [node.clause]
            halflines -= node.hl_max
            continue
        idx = [i for i in range(len(data)) if data[i][1]] + list(node.to_gen())
        clause = None
        for h in range(node.hl_min, halflines + 1):
            with smt.Solver() as solver:
                clause = find_iter(data, domain, idx, find_clause, solver, h)
                if clause is not None:
                    node.hl_max = h
                    node.clause = clause
                    clauses += [clause]
                    halflines -= h
                    saturate(data, domain, node)
                    break;
            node.hl_min += 1
        if clause is None:
            return None
    return smt.And(clauses)

def saturate(data, domain, node):
    strat = SelectionStrategy()
    l = [i for i in range(len(data)) if strat.check_example(domain, node.clause, data[i][0]) == data[i][1]]
    ls = set(l)
    #token = next(node_to_gen(node))
    d = deque([node.get_root()])
    while d:
        n = d.pop()
        if n == node:
            continue
        ns = set(n.to_gen())
        if token in ns:
            #n is transitive parent of node
            d.append(n.left)
            d.append(n.right)
            continue
        intersec = ns.intersection(ls)
        if len(intersec) == len(ns):#all dates in n are consistent with node.clause
            switch(n, node)
        elif len(intersec) != 0:
            assert n.left is not None
            d.append(n.left)
            d.append(n.right)


##HIERARCHICAL LVL 2
def search_lit(data, problem):
    domain = problem.domain
    neg_idx = [i for i in range(len(data)) if not data[i][1]]
    hierarchy_root = build_hierarchy(data, domain, neg_idx)
    cost = 1
    while True:
        q = PriorityQueue()
        q.put(hierarchy_root)
        for clauses in range(1, cost):
            solution = search_in_hierarchy_lit(data, domain, list(q.queue), cost - clauses)
            if solution is not None:
                return solution
            node = q.get()
            br = False
            while node.left is None or (node.hl_max is not None and node.hl_max <= (node.left.hl_min + node.right.hl_min + 1)):
                if node.prio() == float("inf"):
                    br = True
                    break;
                node.priority = None
                q.put(node)
                node = q.get()
            if br:
                break
            if node.left is not None:
                q.put(node.left)
                q.put(node.right)
        cost += 1


def search_in_hierarchy_lit(data, domain, nodes, halflines):
    clauses = []
    for node in nodes:
        if node.hl_min == node.hl_max:
            clauses += [node.clause]
            halflines -= node.hl_max
            continue
        clause = None
        for h in range(node.hl_min, halflines + 1):
            with smt.Solver() as solver:
                clause = search_in_node(data, domain, node, h)
                if clause is not None:
                    node.hl_max = h
                    node.clause = clause
                    clauses += [clause]
                    halflines -= h
                    saturate(data, domain, node)
                    break;
            node.hl_min += 1
        if clause is None:
            return None
    return smt.And(clauses)

def search_in_node(data, domain, node, h):
    if node.solvable == False:
        return None
    if node.literals is None:
        neg_data_gen = node.to_gen()
        possible_pos_lits = domain.bool_vars.copy()
        possible_neg_lits = domain.bool_vars.copy()
        for i in neg_data_gen:
            assert(not data[i][1])
            possible_pos_lits = [l for l in possible_pos_lits if not data[i][0][l]]
            possible_neg_lits = [l for l in possible_neg_lits if data[i][0][l]]
            if not possible_neg_lits and not possible_pos_lits:
                break
        node.literals = [domain.get_symbol(b) for b in possible_pos_lits] + [~domain.get_symbol(b) for b in possible_neg_lits]
        pos_data = [i for i in range(len(data)) if data[i][1]]
        for l in possible_pos_lits:
            pos_data = [i for i in pos_data if not data[i][0][l]]
        for l in possible_neg_lits:
            pos_data = [i for i in pos_data if data[i][0][l]]
        if pos_data:
            node.next_level_node = build_hierarchy(data, domain, pos_data, False)
        #else it stays None


    if node.next_level_node is None:
        return smt.Or(node.literals)
    q = PriorityQueue()
    q.put(node.next_level_node)
    solutions = []
    neg_idx = list(node.to_gen())
    while not q.empty():
        if len(solutions) + len(q.queue) > h:
            return None
        n = q.get()
        if n.clause is not None:
            solutions += [n.clause]
            continue
        if n.hl_min > 1:
            if n.left is None:
                node.solvable = False
                return None
            q.put(n.left)
            q.put(n.right)
            continue
        with smt.Solver() as solver:
            solution = find_iter(data, domain, list(n.to_gen()) + neg_idx,find_hl, solver)
            if solution is None:
                n.hl_min = 2
                if n.left is None:
                    #print("unsatisfiable node!")
                    return None
                q.put(n.left)
                q.put(n.right)
            else:
                solutions += [solution]
                n.clause = solution
                saturate(data, domain, n)
    return smt.Or(solutions + node.literals)
            
        
