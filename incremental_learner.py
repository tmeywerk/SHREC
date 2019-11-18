import random
import time

import pysmt.shortcuts as smt

from smt_check import SmtChecker


class SelectionStrategy(object):
    def select_active(self, domain, data, formula, active_indices):
        raise NotImplementedError()

    @staticmethod
    def check_example(domain, formula, assignment):
        return SmtChecker(assignment).check(formula)


class AllViolationsStrategy(SelectionStrategy):
    def select_active(self, domain, data, formula, active_indices):
        active_set = set(active_indices)
        for i in range(len(data)):
            if i not in active_set:
                learned_label = SelectionStrategy.check_example(domain, formula, data[i][0])
                if learned_label != data[i][1]:
                    yield i


class RandomViolationsStrategy(AllViolationsStrategy):
    def __init__(self, sample_size):
        self.sample_size = sample_size
        self.last_violations = None

    def select_active(self, domain, data, formula, active_indices):
        all_violations = list(AllViolationsStrategy.select_active(self, domain, data, formula, active_indices))
        self.last_violations = all_violations
        sample_size = min(self.sample_size, len(all_violations))
        return random.sample(all_violations, sample_size)

class IndexedAllViolationsStrategy(SelectionStrategy):
    def __init__(self, possible_indices):
        self.possible_indices = possible_indices
        
    def select_active(self, domain, data, formula, active_indices):
        active_set = set(active_indices)
        for i in self.possible_indices:
            if i not in active_set:
                learned_label = SelectionStrategy.check_example(domain, formula, data[i][0])
                if learned_label != data[i][1]:
                    yield i


class IndexedRandomViolationsStrategy(IndexedAllViolationsStrategy):
    def __init__(self, sample_size, possible_indices):
        self.sample_size = sample_size
        self.last_violations = None
        self.possible_indices = possible_indices

    def select_active(self, domain, data, formula, active_indices):
        all_violations = list(IndexedAllViolationsStrategy.select_active(self, domain, data, formula, active_indices))
        self.last_violations = all_violations
        sample_size = min(self.sample_size, len(all_violations))
        return random.sample(all_violations, sample_size)


class WeightedRandomViolationsStrategy(AllViolationsStrategy):
    def __init__(self, sample_size, weights):
        self.sample_size = sample_size
        self.last_violations = None
        self.weights = weights

    def select_active(self, domain, data, formula, active_indices):
        all_violations = list(AllViolationsStrategy.select_active(self, domain, data, formula, active_indices))
        self.last_violations = all_violations
        sample_size = min(self.sample_size, len(all_violations))
        import sampling
        return sampling.sample_weighted(zip(all_violations, [self.weights[i] for i in all_violations]), sample_size)


class MaxViolationsStrategy(AllViolationsStrategy):
    def __init__(self, sample_size, weights):
        self.sample_size = sample_size
        self.last_violations = None
        self.weights = weights

    def select_active(self, domain, data, formula, active_indices):
        all_violations = list(AllViolationsStrategy.select_active(self, domain, data, formula, active_indices))
        self.last_violations = all_violations
        sample_size = min(self.sample_size, len(all_violations))
        weighted_violations = zip(all_violations, [self.weights[i] for i in all_violations])
        weighted_violations = sorted(weighted_violations, key=lambda t: t[1])
        return [t[0] for t in weighted_violations[0:sample_size]]
