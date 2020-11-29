# Simplices: A list of the d+1 simplices of the complex, where each simplex is represented as a frozenset containing its vertices.
# Weights: A dictionary with d-simplices (represented as frozensets) as keys and weights of simplex as value
import networkx

from algorithms.hom_loc_cg import hom_loc_cg
from algorithms.hom_loc_cg_rep import hom_loc_cg_rep
from algorithms.hom_loc_sg import hom_loc_sg
from algorithms.hom_loc_sg_rep import hom_loc_sg_rep
from algorithms.tools.chain_complex import ChainComplex
from numpy.random import RandomState


class HomLoc(object):

    def __init__(self, simplices, weights, cycle=[], full_setup=True, memory_limit=2 ** 20):
        self.memory_limit = memory_limit
        self.weights = weights
        self.up_simplices = simplices
        self.down_simplices = list(self.weights.keys())
        self.chain_complex = None
        self.cycle = cycle
        if full_setup:
            self.compute_treewidth()

    def set_cycle(self, cycle):
        self.cycle = cycle

    def add_noise(self, in_cycle, rs = RandomState(42), uniform_probability=0.5):
        out_cycle = frozenset(in_cycle)
        for simplex in self.up_simplices:
            bnd = self.chain_complex.boundary_map([self.chain_complex.up_id[frozenset(simplex)] for simplex in self.up_simplices if rs.uniform(0, 1) <= uniform_probability])
            out_cycle = frozenset.symmetric_difference(out_cycle, bnd)
        out_cycle = [self.chain_complex.do_simp[simplex] for simplex in out_cycle]
        return list(out_cycle)

    def compute_treewidth(self, connectivity_graph=True, spine_graph=True):
        self.chain_complex = ChainComplex(self.up_simplices, self.down_simplices, self.weights, connectivity_graph,
                                          spine_graph)

    def treewidth_of_spine_graph(self):
        return self.chain_complex.sgTD.tree_width

    def treewidth_of_connectivity_graph(self):
        return self.chain_complex.cgTD.tree_width

    def number_of_bags_in_decomposition_of_spine_graph(self):
        return self.chain_complex.sg_NTD_size()

    def number_of_bags_in_decomposition_of_connectivity_graph(self):
        return self.chain_complex.cg_NTD_size()

    def homology_localization(self, spine_graph=True, print_status=False, output_homologous_cycle=True):
        if spine_graph:
            if output_homologous_cycle:
                return hom_loc_sg_rep(self.chain_complex, self.cycle, print_status, self.memory_limit)
            else:
                return hom_loc_sg(self.chain_complex, self.cycle, print_status, self.memory_limit)
        else:
            if output_homologous_cycle:
                return hom_loc_cg_rep(self.chain_complex, self.cycle, print_status, self.memory_limit)
            else:
                return hom_loc_cg(self.chain_complex, self.cycle, print_status, self.memory_limit)

    def nice_tree_decomposition(self, spine_graph=True):
        if spine_graph:
            return self.chain_complex.sgTD.nice_TD
        else:
            return self.chain_complex.cgTD.nice_TD
