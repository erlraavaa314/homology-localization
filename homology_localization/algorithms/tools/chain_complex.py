# File containing the ChainComplex class and the TD
import networkx as nx
from networkx.algorithms import approximation


class ChainComplex(object):
    """An interface for storing, accessing and generating information about a simplicial complex.

    Instances of this class organizes all relevant information about the input space needed to run the homology
    localization algorithms in this package and it serves as the interface between these algorithms and the input. As an
    example it can be used to apply the boundary operator of the chain complex, to get information about the tree
    decomposition of the spine graph and the connectivity graph of the boundary operator and to get the weight of
    simplices.

    Attributes:
        up_size: The number of d+1 simplices in the simplicial complex
        do_size: The number of d simplices in the simplicial complex
        up_simp: A dictionary for converting the ID's of d+1 simplices to their simplices (represented as frozensets)
        up_id: A dictionary for converting d+1 simplices (represented as frozensets) to their ID
        do_simp: A dictionary for converting the ID's of d simplices to their simplices (represented as frozensets)
        do_id: A dictionary for converting d-simplices (represented as frozensets) to their ID
        si_weig: A dictionary for finding the weight of a d-simplices (represented as frozensets)
        id_weig: A dictionary for finding the weight of a d-simplices given its ID
        bndries: A dictionary for finding the boundary of simplex given its ID
        cg: The connectivity graph of the simplicial complex
        cgTD: A TreeDecomposition of the connectivity graph of the simplicial complex
        sg: The spine graph of the simplicial complex
        sgTD: A TreeDecomposition of the spine graph of the simplicial complex
    """

    def __init__(self, simplex_up, simplex_down, down_weights, connectivity_graph=True, spine_graph=True):

        # The number of d+1 simplices
        self.up_size = len(simplex_up)

        # The number of d simplices
        self.do_size = len(simplex_down)

        # The dict takes ID to d+1 simplex
        self.up_simp = {index: frozenset(simplex_up[index]) for index in range(0, len(simplex_up))}

        # The dict takes d+1 simplex to ID
        self.up_id = {frozenset(simplex_up[index]): index for index in range(0, len(simplex_up))}

        # The dict takes ID to d simplex
        self.do_simp = {index: frozenset(simplex_down[index]) for index in range(0, len(simplex_down))}

        # The dict takes d simplex to ID
        self.do_id = {frozenset(simplex_down[index]): index for index in range(0, len(simplex_down))}

        # The dict takes d simplex to weight
        self.si_weig = down_weights

        # The dict takes ID of d simplex to weight
        self.id_weig = {index: self.si_weig[self.do_simp[index]] for index in self.do_simp}

        # The dict takes d+1 simplex to its boundary (as a frozen set)
        self.bndries = {index: self.boundary(index) for index in range(0, len(simplex_up))}

        if connectivity_graph:
            # The conectivity graph of the simplicial complex
            self.cg = self.con_graph()

            # The (nice and normal) treedecomposition of the connectivity graph
            self.cgTD = TD(self.cg)
            self.cgTD.get_niceTD()

        if spine_graph:
            # The spine graph of the simplicial complex
            self.sg = self.spine_graph()

            # The treedecomposition of the d-spine graph
            self.sgTD = TD(self.sg)
            self.sgTD.get_niceTD()

    def number_of_d_pluss_1_simplices(self):
        """Returns the number of d+1 simplices."""
        return self.up_size

    # Gets the weight of a d-simplex
    def get_weight(self, simplex_id):
        """Returns the weight of a d-simplex."""
        return self.id_weig[simplex_id]

    def get_id_d_simplex(self, simplex):
        """Returns the ID of a d-simplex."""
        return self.do_id[simplex]

    def get_id_d_simplices(self, simplices):
        """Returns the ID's of a set of d-simplices (as a frozenset)."""
        return frozenset(self.do_id[simplex] for simplex in simplices)

    def get_weight_set(self, simplices):
        """Returns the weight of a set of d-simplices."""
        return sum([self.get_weight(simplex) for simplex in simplices])

    def get_bnd(self, simplex_id):
        """Returns the boundary of a d+1-simplex."""
        return self.bndries.get(simplex_id)

    def boundary(self, simplex_id):
        """Finds the boundary of a d+1-simplex without the dictionary."""
        simplex = self.up_simp[simplex_id]
        bnd_set = [frozenset.difference(simplex, frozenset([elem])) for elem in simplex]
        bnd = frozenset([self.do_id[simplex] for simplex in bnd_set])
        return bnd

    def boundary_map(self, simplices):
        """Finds the boundary (represented as a frozenset of frozensets) of a frozenset of d+1 simplices."""
        boundary = frozenset([])
        for simplex in simplices:
            boundary = frozenset.symmetric_difference(boundary, self.boundary(simplex))
        return boundary

    def d_skeleton(self, simplices):
        """Finds the set of d-faces of a set of simplices."""
        skel = frozenset([])
        for simplex in simplices:
            skel = frozenset.union(skel, self.get_bnd(simplex))
        return skel

    def is_cg_edge(self, simp1, simp2):
        """Checks if a pair of d+1 simplices are adjacent in the connectivity graph."""
        intersection = frozenset.intersection(self.get_bnd(simp1), self.get_bnd(simp2))
        return intersection != frozenset([]) and simp1 != simp2

    def con_graph(self):
        """Makes the connectivity graph from the simplicies."""
        nodes = list(range(0, self.up_size))
        edges = [(a, b) for a in nodes for b in nodes if self.is_cg_edge(a, b)]
        graph = nx.Graph()
        graph.add_nodes_from(nodes)
        graph.add_edges_from(edges)
        return graph

    def spine_graph(self):
        """Makes the spine graph from the simplicies."""

        # Makes the nodes for the d+1 simplices
        nodes_up = list(zip(list(range(0, self.up_size)), [True for i in range(0, self.up_size)]))

        # Makes the nodes for the d simplices
        nodes_down = list(zip(list(range(0, self.do_size)), [False for i in range(0, self.do_size)]))

        # Initializes the graph and ads nodes
        graph = nx.Graph()
        graph.add_nodes_from(nodes_up)
        graph.add_nodes_from(nodes_down)

        # Adds the edges for every d+1 simplex
        for node in nodes_up:
            bnd = self.get_bnd(node[0])
            for down in bnd:
                d = tuple([down, False])
                graph.add_edge(node, d)
        return graph

    def get_NTD_cg(self):
        """Returns the chosen nice tree decomposition of the connectivity graph."""
        return self.cgTD.nice_TD

    def get_NTD_sg(self):
        """Returns the chosen nice tree decomposition of the spine graph."""
        return self.sgTD.nice_TD

    def cg_NTD_size(self):
        """Returns the number of bags in the nice tree decomposition of the connectivity graph."""
        return len(self.cgTD.nice_TD.nodes)

    def sg_NTD_size(self):
        """Returns the number of bags in the nice tree decomposition of the spine graph."""
        return len(self.sgTD.nice_TD.nodes)

    def cg_bag_type(self, bag_id):
        """Returns the bag type of a bag id in the nice tree decomposition of the connectivity graph."""
        return self.cgTD.bag_type(bag_id)

    def sg_bag_type(self, bag_id):
        """Returns the bag type of a bag id in the nice tree decomposition of the spine graph."""
        return self.sgTD.bag_type(bag_id)

    def cg_bag_content(self, bag_id):
        """Returns the ID's of vertices in the bag in the nice tree decomposition of the connectivity graph."""
        return self.cgTD.bag(bag_id)

    def sg_bag_content(self, bag_id):
        """Returns the ID's of vertices in the bag in the nice tree decomposition of the spine graph."""
        return self.sgTD.bag(bag_id)

    def cg_children(self, bag_id):
        """Returns the ID's of the children of a bag in the nice tree decomposition of the connectivity graph."""
        return self.cgTD.children(bag_id)

    def sg_children(self, bag_id):
        """Returns the ID's of the children of a bag in the nice tree decomposition of the spine graph."""
        return self.sgTD.children(bag_id)

    def cg_difference(self, bag_id1, bag_id2):
        """Returns the elements of the first bag that are not in the second bag of the connectivity graph."""
        return self.cgTD.get_difference(bag_id1, bag_id2)

    def sg_difference(self, bag_id1, bag_id2):
        """Returns the elements of the first bag that are not in the second bag of the spine graph."""
        return self.sgTD.get_difference(bag_id1, bag_id2)

    def sg_simplex_up(self, simplex):
        """Checks if a node in the spine graph corresponds to a d+1-dimensional simplex."""
        x, y = simplex
        return y

    def sg_cofaces(self, simplex):
        """Returns the d+1-cofaces of the input d-simplex in a frozen set."""
        return frozenset(self.sg.neighbors(simplex))


class TD(object):
    """An interface for storing, accessing and generating information about the tree decompositions of a graph.

     Objects of this class computes and stores (nice) tree decompositions and provides an interface for getting
     information about the bags of these tree decompositions.

    Attributes:
        G: The underlying graph that we get a tree decomposition of.
        tree_width: The tree width of the tree decomposition we are currently working with.
        tree_decomposition: The tree decomposition we are currently working with which is generally not nice.
        nice_TD: A nice tree decomposition made from the tree decomposition above.
        id_to_bag: A dictionary for associating a bag to each bag ID.
        id_to_type: A dictionary for associating a bag type to each bag ID.
        topord: A list giving a topological ordering of the bags in the nice tree decomposition rooted at an empty bag.
        toporddict: A dictionary giving the position of a bag in the topological ordering.
        """

    def __init__(self, graph):
        self.G = graph

        # Get treedecomposition using the first (min_degree) heuristic
        tw1 = approximation.treewidth.treewidth_min_degree(self.G)

        # Get treedecomposition using the second (fill_in) heuristic
        tw2 = approximation.treewidth.treewidth_min_fill_in(self.G)

        # We let the treedecomposition and treewidth be the smallest of the two heuristics
        if tw1[0] < tw2[0]:
            # The tree width of the input
            self.tree_width = tw1[0]

            # The tree decomposition of the input
            self.tree_decomposition = tw1[1]
        else:
            # The tree width of the input
            self.tree_width = tw2[0]

            # The tree decomposition of the input
            self.tree_decomposition = tw2[1]


        self.nice_TD = None

        self.id_to_bag = None

        self.id_to_type = None

        self.topord = None

        self.toporddict = None

    def get_niceTD(self):
        """Computes and stores a nice tree decomposition"""
        self.nice_TD = nx.Graph()

        # Topologically sorts the nodes of the "bad" treedecompositions
        topord = list(nx.dfs_postorder_nodes(self.tree_decomposition))

        # Makes a dictionary, saying which bag has which position in the "bad" treedecompositions for easy comparisons later on
        toporddict = dict(zip(topord, list(range(0, len(topord)))))

        # Initializes a new index dictionary to look up which index the child of a bag will have in the end.
        index_dict = {}
        # Initializes bag id to bag dictionary
        self.id_to_bag = {}
        # Initializes bag id to bag type (leaf, introduce, forget etc.)
        self.id_to_type = {}
        # Initializes the index of the bag we are currently working on

        index = 0
        for node in topord:
            children = [neigh for neigh in self.tree_decomposition.neighbors(node) if
                        toporddict[neigh] < toporddict[node]]
            childless = False
            if len(children) == 0:
                childless = True
                children.append(frozenset())
                self.nice_TD.add_node(index)
                self.id_to_bag[index] = frozenset()
                self.id_to_type[index] = "leaf"
                index = index + 1

            join_id = []
            for child in children:

                if childless:
                    child_index = index - 1
                else:
                    child_index = index_dict[child]

                # The elements that are in child and not in node
                remove = frozenset.difference(child, node)

                # The elements that are in node but not in child
                add = frozenset.difference(node, child)

                for element in remove:
                    child = frozenset.difference(child, frozenset([element]))
                    self.id_to_bag[index] = child
                    self.id_to_type[index] = "forget"
                    self.nice_TD.add_node(index)
                    self.nice_TD.add_edge(child_index, index)
                    child_index = index
                    index = index + 1

                for element in add:
                    child = frozenset.union(child, frozenset([element]))
                    self.id_to_bag[index] = child
                    self.id_to_type[index] = "introduce"
                    self.nice_TD.add_node(index)
                    self.nice_TD.add_edge(child_index, index)
                    child_index = index
                    index = index + 1

                if child != node:
                    print("Something is wrong.")

                join_id.append(index - 1)

            while len(join_id) != 1:
                a = join_id.pop()
                b = join_id.pop()
                join_id.append(index)
                self.id_to_bag[index] = node
                self.id_to_type[index] = "join"
                self.nice_TD.add_node(index)
                self.nice_TD.add_edge(a, index)
                self.nice_TD.add_edge(b, index)
                index = index + 1

            index_dict[node] = join_id[0]

        child = topord[-1]
        index = index_dict[child] + 1

        for element in child:
            current = frozenset.difference(child, frozenset([element]))
            self.id_to_bag[index] = current
            self.id_to_type[index] = "forget"
            self.nice_TD.add_node(index)
            self.nice_TD.add_edge(index - 1, index)
            child = current
            index = index + 1

        self.topord = list(nx.dfs_postorder_nodes(self.nice_TD, len(self.nice_TD.nodes()) - 1))
        self.toporddict = dict(zip(self.topord, list(range(0, len(self.topord)))))

    def get_children(self, node):
        """Returns a list of the children of a bag in the topological ordering of the (not nice) tree decomposition."""
        return [neigh for neigh in self.tree_decomposition.neighbors(node) if
                self.toporddict[neigh] < self.toporddict[node]]

    def children(self, node):
        """Returns a list of the children of a bag in the topological ordering of the nice tree decomposition."""
        return [neigh for neigh in self.nice_TD.neighbors(node) if neigh < node]

    def bag(self, bag_id):
        """Finds the  elements of a bag."""
        return self.id_to_bag[bag_id]

    def bag_type(self, bag_id):
        """Finds the type of a bag."""
        return self.id_to_type[bag_id]

    def get_difference(self, bag_id1, bag_id2):
        """Finds the difference between the elements of two bags."""
        return frozenset.difference(self.id_to_bag[bag_id1], self.id_to_bag[bag_id2])
