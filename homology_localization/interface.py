from homology_localization.algorithms.hom_loc import HomLoc


def localize(simplices, weights, cycle, hasse_diagram=True, memory_limit=2 ** 20):
    homloc_obj = HomLoc(simplices, weights, cycle, True, memory_limit)
    return homloc_obj.homology_localization(hasse_diagram)


def treewidth(simplices, weights, hasse_diagram=True):
    homloc_obj = HomLoc(simplices, weights, [])
    if hasse_diagram:
        return homloc_obj.treewidth_of_spine_graph()
    else:
        return homloc_obj.treewidth_of_connectivity_graph()


def number_of_bags_in_treedecomposition(simplices, weights, hasse_diagram=True):
    homloc_obj = HomLoc(simplices, weights, [])
    if hasse_diagram:
        return homloc_obj.number_of_bags_in_decomposition_of_spine_graph()
    else:
        return homloc_obj.number_of_bags_in_decomposition_of_connectivity_graph()
