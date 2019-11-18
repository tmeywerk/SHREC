from collections import deque
import scipy.cluster.hierarchy as shc
import numpy as np

BOOL_VAL = 1.0

class HierarchyNode:
    def __init__(self, left, right, priority, date = None):
        self.left = left
        self.right = right
        self.priority = priority
        self.date = date
        self.hl_min = 0
        self.hl_max = None
        self.clause = None
        self.parent = None
        self.index = None
        self.next_level_node = None
        self.literals = None
        self.solvable = True

    def set_parents(self):
        if self.left is not None:
            self.left.parent = self
            self.right.parent = self

    def switch_prio(self):
        if self.priority is not None:
            self.priority *= -1

    def set_index(self):
        if self.parent is None:
            self.index = 1
        else:
            #set both because we dont actually know which one we are right now
            self.parent.left.index = self.parent.index * 2
            self.parent.right.index = self.parent.index * 2 + 1
        

    def prio(self):
        return float("inf") if self.priority is None else self.priority

    def __lt__(self, other):
        return self.prio() < other.prio()
    def __le__(self, other):
        return self.prio() <= other.prio()
    def __gt__(self, other):
        return self.prio() > other.prio()
    def __ge__(self, other):
        return self.prio() >= other.prio()
    def __eq__(self, other):
        return self.index == other.index

    def str(self):
        if self.date is not None:
            return self.date
        else:
            return "({},{})".format(self.left.str(), self.right.str())

    def add_child(self, c):
        copy = HierarchyNode(self.left, self.right, self.priority, self.date)
        copy.hl_min = self.hl_min
        copy.hl_max = self.hl_max
        copy.clause = self.clause
        copy.index = self.index * 2
        self.left = copy
        copy.parent = self
        self.right = c
        c.index = self.index * 2 + 1
        c.parent = self
        self.date = None

    def remove_child(self, left):
        assert(self.left is not None)
        if left:
            res = self.left
            if self.right.date is None:
                self.left = self.right.left
                self.right = self.right.right
                self.left.parent = self
                self.right.parent = self
                self.left.set_index()
            else:
                self.date = self.right.date
                self.left = None
                self.right = None
            return res
        else:
            res = self.right
            if self.left.date is None:
                self.right = self.left.right
                self.left = self.left.left
                self.left.parent = self
                self.right.parent = self
                self.left.set_index()
            else:
                self.date = self.left.date
                self.left = None
                self.right = None
            return res

    def get_root(self):
        r = self
        while r.parent is not None:
            r = r.parent
        return r

    def to_gen(self):
        d = deque([self])
        while d:
            n = d.pop()
            if n.date is not None:
                yield n.date
            else:
                d.append(n.left)
                d.append(n.right)
                


def build_hierarchy(data, domain, idx, use_bool = True):
    vectors = []
    nodes = [HierarchyNode(None, None, None, i) for i in idx]
    if len(nodes) == 1:
        nodes[0].switch_prio()
        nodes[0].set_parents()
        nodes[0].set_index()
        return nodes[0]
    for n in nodes:
        if use_bool:
            v = [BOOL_VAL if data[n.date][0][b] else 0 for b in domain.bool_vars]
        else:
            v = []
        for r in domain.real_vars:
            lo, hi = domain.var_domains[r]
            v += [data[n.date][0][r]/(hi - lo)]
        vectors += [v]
    input_vecs = np.array(vectors)
    dendrogram = shc.linkage(input_vecs, method="average", metric="cityblock")
    for cl in dendrogram:
        new_node = HierarchyNode(nodes[int(cl[0])], nodes[int(cl[1])], cl[2])
        nodes += [new_node]

    for node in nodes:
        node.switch_prio()
        node.set_parents()
        node.set_index()
    return nodes[len(nodes) - 1] # root


def switch(node, new_parent):
    l = node.parent.left == node
    new_parent.add_child(node.parent.remove_child(l))
    node.set_index()
