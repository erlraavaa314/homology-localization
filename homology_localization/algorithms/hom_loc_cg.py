from homology_localization.algorithms.error_file import MemoryLimitViolation
from homology_localization.algorithms.tools.bit_magic import MyUniverse, Translator
import math

def hom_loc_cg(cc, v_set, give_status, memory_limit):

    memory = 0
    memory_peak = 0
    v = cc.get_id_d_simplices(v_set)

    # Initialises a dictionary of tables that will be filled in recursively
    tables = {}
    u = {}

    for bag_id in range(0, cc.cg_NTD_size()):
        u0 = MyUniverse()
        u1 = MyUniverse()
        u[bag_id] = {0: u0, 1: u1}

    # This ordering of bag ID's works because this ordering is topological.
    for bag_id in range(0, cc.cg_NTD_size()):
        bag_type = cc.cg_bag_type(bag_id)
        children_id = cc.cg_children(bag_id)
        parsed = False

        # The base case where there is only one table entry to fill, the one containing one entry where Q,P=emptyset:
        if bag_type == "leaf" and len(children_id) == 0:
            # Looking up the value at bag id in the table we get, (Q = Ø -> (P = Ø -> solution value = 0).

            tables[bag_id] = {0: {0: 0.0}}
            memory = memory + 1
            parsed = True

        # Introducing a new simplex to the bag
        if bag_type == "introduce" and len(children_id) == 1:
            child_table = tables[children_id[0]]
            tables[bag_id], memory = introduce(child_table, bag_id, children_id[0], cc, v, u, memory, memory_limit)
            parsed = True

        # Forgetting an old simplex in the bag
        if bag_type == "forget" and len(children_id) == 1:
            child_table = tables[children_id[0]]
            tables[bag_id], memory = forget(child_table, bag_id, children_id[0], cc, v, u, memory, memory_limit)
            parsed = True

        # Joining two equal bags
        if bag_type == "join" and len(children_id) == 2:
            child_bag_id = cc.cg_children(bag_id)
            child_table1 = tables[children_id[0]]
            child_table2 = tables[children_id[1]]
            tables[bag_id], memory = join(child_table1, child_table2, bag_id, child_bag_id, cc, v, u, memory, memory_limit)
            parsed = True

        # Make this an error message:
        if not parsed:
            print("Mismatch between bagtype and number of children at bag", bag_id, bag_type)

        if give_status:
            optimal = math.inf
            for q in tables[bag_id]:
                for p in tables[bag_id][q]:
                    value = tables[bag_id][q][p]
                    optimal = min(optimal, value)

            print("The ", bag_id, "'th bag of type ", cc.cg_bag_type(bag_id), " and of size ",
                  len(cc.cg_bag_content(bag_id)), " has an optimal solution of size ", optimal, " and children ",
                  children_id)

        memory_peak = max(memory, memory_peak)
        for child_id in children_id:
            child_tab = tables.pop(child_id)
            for entry in child_tab:
                memory = memory - len(child_tab[entry])

    check1 = False

    check2 = False

    check3 = False

    # We get the table for the root bag which should contain precisely one entry for the empty set
    root_table = tables[cc.cg_NTD_size() - 1]
    if len(root_table) == 1:
        # print("The root table is of correct size")
        check1 = True

    # This table should contain a list containing a triple p = Ø, a rep. solution and the value of that solution
    entries = root_table[0]

    if len(entries) == 1:
        # print("The number of entries at Q = Ø is correct")
        check2 = True
    p = 0

    sol = entries[p]

    if p == 0:
        # print("p is empty at root")
        check3 = True

    if check1 and check2 and check3:
        allgood = True
        # print("All seemingly good")

    # print(tables)

    d_skel = cc.d_skeleton(frozenset(range(0, cc.number_of_d_pluss_1_simplices())))
    uncounted = frozenset.difference(v, d_skel)
    print([cc.do_simp[x] for x in uncounted])
    new_sol = sol + cc.get_weight_set(uncounted)
    return new_sol, memory_peak


def introduce(child_table, bag_id, child_id, cc, v, u, memory, memory_limit):
    u[bag_id][0] = u[child_id][0]
    u[bag_id][1] = u[child_id][1]

    # The introduced simplex
    sigma_set = cc.cg_difference(bag_id, child_id)

    # A check on the length of sigma_set
    if len(sigma_set) != 1:
        print("The introduce bag introduces either more or fewer than one simplex")

    # "Unpack" the simplex from the set
    sigma, *_ = sigma_set

    # The boundary of the introduced simplex (as a frozenset)
    bnd_sig = cc.get_bnd(sigma)

    # The simplices of the child bag
    child_bag = cc.cg_bag_content(child_id)

    # The skeleton of the child bag
    skel_child = cc.d_skeleton(child_bag)

    # The newly "added" d-simplices
    new_d = frozenset.difference(bnd_sig, skel_child)

    # The newly "added" d-simplices of v
    new_v = frozenset.intersection(v, new_d)

    # Initializing the table that will be filled out
    table = {}

    u[bag_id][0].add_element(sigma, 0.0)
    sigma_set_int = u[bag_id][0].set_to_int(sigma_set)

    list_new_d = list(new_d)
    cost_of_new_d = [cc.get_weight(d) for d in list_new_d]

    u[bag_id][1].add_elements(zip(list_new_d, cost_of_new_d))
    new_v_int = u[bag_id][1].set_to_int(new_v)
    bnd_sig_int = u[bag_id][1].set_to_int(bnd_sig)

    # For every subset of nodes in the child bag
    for q in child_table:

        # The set q union sigma
        q_sig_int = u[bag_id][0].union(q, sigma_set_int)

        # Make a dictionary for q and q_sigma
        table[q] = {}
        table[q_sig_int] = {}

        # For every entry in the dictionary of q in the child bag
        for p in child_table[q]:
            value = child_table[q][p]

            # Extend the guessed d simplices and its representative solution/ solution value
            p_extended_int = u[bag_id][1].union(p, new_v_int)

            value_extended = value + u[bag_id][1].cost(new_v_int)

            # Make a new entry in the dictionary
            # table[q][p_extended] = (rep_extended, value_extended)
            table[q][p_extended_int] = value_extended

            # Repeat the above procedure but for q union sigma instead
            p_sig_int = u[bag_id][1].sym_dif(p_extended_int, bnd_sig_int)

            value_sig = value - u[bag_id][1].cost(p) + u[bag_id][1].cost(p_sig_int)
            table[q_sig_int][p_sig_int] = value_sig

            memory = memory + 2
            if memory > memory_limit:
                raise MemoryLimitViolation

    return table, memory


def forget(child_table, bag_id, child_id, cc, v, u, memory, memory_limit):
    u[bag_id][0] = u[child_id][0]
    u[bag_id][1] = u[child_id][1]

    # The forgotten simplex
    sigma_set = cc.cg_difference(child_id, bag_id)

    # A check on the length of sigma_set
    if len(sigma_set) != 1:
        print("The introduce bag introduces either more or fewer than one simplex")

    # "Unpack" the simplex from the set
    sigma, *_ = sigma_set

    # The boundary of the forgotten simplex (as a frozenset)
    bnd_sig = cc.get_bnd(sigma)

    # The simplices of the current bag
    bag = cc.cg_bag_content(bag_id)

    # The skeleton of the current bag
    skel_bag = cc.d_skeleton(bag)

    # The newly "removed" d-simplices
    bound_sig_old = frozenset.difference(bnd_sig, skel_bag)

    # Initializing the table that will be filled out
    table = {}

    sigma_set_int = u[bag_id][0].set_to_int(sigma_set)
    bound_sig_old_int = u[bag_id][1].set_to_int(bound_sig_old)

    # For every entry in the dictionary of q in the child bag
    for q in child_table:
        q_sig_int = u[bag_id][0].dif(q, sigma_set_int)

        # Checks if there is a list at table[q_sig] already
        if not q_sig_int in table:
            # If this is not the case, initializes this list
            table[q_sig_int] = {}

        # For every triple in the list at the child, q, we compute the new p_sig
        for p in child_table[q]:
            value = child_table[q][p]

            p_sig_int = u[bag_id][1].dif(p, bound_sig_old_int)

            # We check if the new p_sig is already in the list of tuples stored at q_sig. If it is we compare it to the old one and update it if neccessary
            if p_sig_int in table[q_sig_int]:
                value_other = table[q_sig_int][p_sig_int]
                if value < value_other:
                    table[q_sig_int][p_sig_int] = value

            # If no match for p_sig was found we add it to the list.
            else:
                table[q_sig_int][p_sig_int] = value
                memory = memory + 1
                if memory > memory_limit:
                    raise MemoryLimitViolation

    u[bag_id][0].remove_element(sigma)
    u[bag_id][1].remove_elements(bound_sig_old)
    return table, memory


def join(child_table1, child_table2, bag_id, child_bag_id, cc, v, u,  memory, memory_limit):
    u[bag_id][0] = u[child_bag_id[0]][0]
    u[bag_id][1] = u[child_bag_id[0]][1]

    u2q = u[child_bag_id[1]][0]
    u2p = u[child_bag_id[1]][1]

    # Translates opposite ways!
    tq = Translator(u[bag_id][0], u2q)
    tp = Translator(u2p, u[bag_id][1])

    # Gets the d+1 simplices of the bag
    bag = cc.cg_bag_content(bag_id)

    # Gets V intersected with the current bag
    v_bag = frozenset.intersection(v, cc.d_skeleton(bag))

    # Initializes the table that will be filled out during this call
    table = {}

    v_bag_int = u[bag_id][1].set_to_int(v_bag)

    for q in child_table1:

        # Initializes the list at q
        table[q] = {}

        q_elems = u[bag_id][0].int_to_set(q)

        # Gets the boundary of q
        bound_q = cc.boundary_map(q_elems)

        bound_q_int = u[bag_id][1].set_to_int(bound_q)

        q2 = tq.int_to_int(q)

        # For every entry at Q in left bag
        for p1 in child_table1[q]:
            val1 = child_table1[q][p1]

            # Compute the cost of p1
            cost_p1 = u[bag_id][1].cost(p1)

            # For every entry at Q in the right bag
            for p2 in child_table2[q2]:

                p2_transformed = tp.int_to_int(p2)
                val2 = child_table2[q2][p2]

                # Compute the cost of p2 in that bag
                cost_p2 = u2p.cost(p2)

                # Compute the new representative

                p_new_int = u[bag_id][1].sym_dif(p1, u[bag_id][1].sym_dif(p2_transformed,
                                                                          u[bag_id][1].sym_dif(bound_q_int, v_bag_int)))

                # Compute the value of that solution
                new_value = val1 + val2 - cost_p1 - cost_p2 + u[bag_id][1].cost(p_new_int)

                # Keep track of if this entry is already filled

                if p_new_int in table[q]:
                    value_other = table[q][p_new_int]
                    if new_value < value_other:
                        table[q][p_new_int] = new_value

                # If no match for p_sig was found we add it to the list.
                else:
                    table[q][p_new_int] = new_value
                    memory = memory + 1
                    if memory > memory_limit:
                        raise MemoryLimitViolation

    return table, memort

