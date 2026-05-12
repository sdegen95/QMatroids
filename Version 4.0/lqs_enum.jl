################################################################################
##  Enumeration using linear q-subclass selectors
################################################################################
include("helper_functions.jl")
include("q_matroids.jl")
include("q_properties.jl")

###########################################################################################
# Updated Version!!!
# Using Julia-version 1.12.6
# Using Oscar-version 1.7.2
# They will currently not run locally!!!!!!!
# Just for the sever at the moment!!!!!!!!
###########################################################################################

################################################################################
## Helper function for the deep first search algo
################################################################################

@doc raw"""
    Lex_compare_subs(sub1:: Any, sub2::Any)

    This compares the two subspaces `sub1` and `sub2` w.r.t. to the specific linear order that compares each row from top to bottom w.r.t. lex-order.
    It assume in the beginning that `sub1`<`sub2` and return `true` if it is and `false` if `sub1`>`sub2`. 
    Note that the subspaces need to have the same dimension!!!
"""
function Lex_compare_subs(sub1:: Any, sub2::Any)
    # Lift subspaces
    sub1t = map(lift, sub1)
    sub2t = map(lift, sub2)
    sub1_smaller_sub2 = true
    r = rank(sub1)

    for i in range(1,r)
        row1i = sub1t[i,:]
        row2i = sub2t[i,:]
        diff_vec = row1i-row2i
        
        if iszero(diff_vec) == false
            #println("here")
            firstpos = findfirst(x -> x != 0, diff_vec)
            
            if diff_vec[firstpos] < 0
                break
                
            elseif diff_vec[firstpos] > 0
                sub1_smaller_sub2 = false
                break

            end
        end
        
    end

    return sub1_smaller_sub2

end
################################################################################


@doc raw"""
    Q_Matroid_base_enc(base:: Any, kspaces::Any)

    This takes in the bases of a q-matroid of rank k and outputs the 0-1-encoding vector among all k-spaces.
    In particular if a k-space gets a one if its a bases and zero else. 
"""
function Q_Matroid_base_enc(bases:: Any, kspaces::Any)
    num_k_spaces = length(kspaces)
    enc_vec = ones(Int,num_k_spaces)
    for (id,elm) in enumerate(kspaces)
        if !(elm in bases)
            enc_vec[id]=0
        end
    end

    return enc_vec
end
################################################################################

@doc raw"""
    Q_Matroid_linear_q_subclasses(QM::Q_Matroid)

    This returns the collection of all linear q-subclasses of a given q-matroid.
"""

function Q_Matroid_linear_q_subclasses(QM::Q_Matroid, hyps)

    # Rank of q-matroid
    if length(QM.bases)!= 0
        q_rank = rank(QM.bases[1])
    else
        q_rank = 0
    end

    # Associated notions
    indeps = Q_Matroid_Independentspaces(QM)
    deps = Q_Matroid_Dependentspaces(QM)
    #hyps = Q_Matroid_Hyperplanes(QM)
    hyps_subs = [AbstractVector{Any}(x) for x in collect(powerset(hyps)) if AbstractVector{Any}(x)!=[] && AbstractVector{Any}(x)!=hyps]

    # For every subset in "hypers_subs" we check the linear q-subclass condition and collect all 
    lqs_col = AbstractVector{Any}([[],hyps])
    for sub in hyps_subs
        if length(sub) == 1
            push!(lqs_col,sub)
        else
            counter = 0
            for combi in Oscar.combinations(sub,2)
                inters = inters_vsV3(combi[1],combi[2])
                inters_rank = Q_Matroid_Ranks(QM,inters,indeps,deps)
                #println(inters,inters_rank)
                if inters_rank == q_rank-2
                    superhyps = intersect(containments_fix_spaceV2(inters),hyps)
                    if issubset(superhyps, sub) == false
                        counter += 1
                    end
                    #println(superhyps)
                end
            end
            if counter == 0
                push!(lqs_col,sub)
            end
        end
    end 

    return unique!(lqs_col)
end
################################################################################

@doc raw"""
    Initial_linear_q_subclasses(hyps::Any, lqs_collection::Any, dim::Any, field::Any)

    This returns the collection of all linear q-subclasses that are need for an initial input in the below algo.
"""

function Initial_linear_q_subclasses(hyps::Any, lqs_collection::Any, dim::Any, field::Any) 

    # Compute automorphism group of QM
    GLn = Oscar.general_linear_group(dim, field)
    hyps_set = Set(hyps)

    actfn = function(spaces,G)
        return Set([rref(C*transpose(matrix(G)))[2] for C in spaces])
    end

    #S, emb = stabilizer(GLn, hyps_set, actfn)
    S = [g for g in GLn if actfn(Set(hyps),g)==Set(hyps)]

    # Compute the orbits of the lqs under the action of S
    # Appearing lqs in some orbit get removed from the lqs_collection

    init_lqs_collection = []
    seen_list = []
    for l in lqs_collection
        if !(Set(l) in seen_list)
            push!(init_lqs_collection,l)
            for s in S
                act_l = actfn(Set(l),s)
                push!(seen_list,act_l)
            end
        end
    end
    
    #return S, emb, init_lqs_collection
    return init_lqs_collection
    
end

@doc raw"""
    Initial_linear_q_subclassesV2(hyps::Any, lqs_collection::Any, dim::Any, field::Any)

    This returns the collection of all linear q-subclasses that are need for an initial input in the below algo.
"""

function Initial_linear_q_subclassesV2(hyps::Any, lqs_collection::Any, dim::Any, field::Any) 

    # Compute automorphism group of QM
    GLn = Oscar.general_linear_group(dim, field)
    hyps_set = Set(hyps)

    actfn = function(spaces,G)
        return Set([rref(C*matrix(G))[2] for C in spaces])
    end

    S, emb = stabilizer(GLn, hyps_set, actfn)
    #S = [g for g in GLn if actfn(Set(hyps),g)==Set(hyps)]

    # Compute the orbits of the lqs under the action of S
    # Appearing lqs in some orbit get removed from the lqs_collection

    init_lqs_collection = []
    seen_list = []
    for l in lqs_collection
        if !(Set(l) in seen_list)
            push!(init_lqs_collection,l)
            for s in S
                act_l = actfn(Set(l),s)
                push!(seen_list,act_l)
            end
        end
    end
    
    #return S, emb, init_lqs_collection
    return init_lqs_collection
    
end
################################################################################

@doc raw"""
    Hyperplane_induced_partition(space::Any, ones_dict::Any)

    This inputs a `space` H and a non-empty dictionary of one-spaces `ones_dict`.
    It outputs a partition p_H=(B_1,...,B_n) of the one-spaces w.r.t. to the rule: e_i,e_j in B_n if H+e_i = H+e_j.  
"""
function Hyperplane_induced_partition(space::Any, ones_dict::Any)
    partition = []
    seen_list = AbstractVector{Any}([])
    ones = values(ones_dict)

    # Get the partition in terms of one-spaces
    for e in ones
        if !(e in seen_list)
            sum = sum_vsV2(space,e)
            ones_sum = intersect(dim_one_subs(sum),ones)
            block = AbstractVector{Any}([])
            for x in ones_sum
                push!(seen_list,x)
                push!(block,x)
            end
            push!(partition,block)
        end
    end

    # Transform the above partition into a partition using the dict indices
    new_partition = []
    indices = keys(ones_dict)

    for b in partition
        new_b = []
        for x in b
            ind_x = [ind for ind in indices if ones_dict[ind] == x]
            new_b = vcat(new_b,ind_x)
        end
        push!(new_partition,sort(new_b))
    end

    return new_partition
end
################################################################################
@doc raw"""
    DFS_restrictions_dict(ind:: Any, lqs:: Any, hyp_partition_dict:: Any, max_depth:: Any)

    ....
"""

function DFS_restrictions_dict(ind:: Any, lqs:: Any, hyp_partition_dict:: Any, max_depth:: Any)
    restrictions_list = [[num,[],[]] for num in range(1,max_depth)]

    # Compute restriction for the other indicies bases on the current one `ind`
    for key in keys(hyp_partition_dict)
        partition = hyp_partition_dict[key]
        ind_block = partition[findall(x -> issubset(ind,x), partition)[1]]
        #println(ind_block)
        if key in lqs
            for x in ind_block
                if !(x in range(1,ind))
                    for elm in restrictions_list
                        if elm[1]==x 
                            push!(elm[2],key)
                        end
                    end
                end
            end
        else
            for x in ind_block
                if !(x in range(1,ind))
                    for elm in restrictions_list
                        if elm[1]==x 
                            push!(elm[3],key)
                        end
                    end
                end
            end
        end
    end

    # Transform list into dictionary for better accessability 
    restrictions_dict = OrderedDict([elm[1] => [elm[2],elm[3]] for elm in restrictions_list])

    return restrictions_dict
end
################################################################################

@doc raw"""
    DFS_possible_options(ind:: Any, lqs_collection:: Any, restrictions_dict:: Any)

    ....
"""

function DFS_possible_options(ind:: Any, lqs_collection:: Any, restrictions_dict:: Any)
    lqs_options = []
    restrictions_pos = restrictions_dict[ind][1]
    restrictions_neg = restrictions_dict[ind][2]

    for elm in lqs_collection
        if issubset(restrictions_pos,elm) && length(intersect(restrictions_neg,elm))==0
            push!(lqs_options,elm)
        end
    end

    return lqs_options
end

################################################################################
## DPS-Enumeration-Algo for a fixed q-matroid: Recursive approach
################################################################################

@doc raw"""
    DFS_LIFO(current_node:: Any, stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any, v_results::Any)

    ....
"""
function DFS_LIFO(current_node:: Any, stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any, v_results::Any)
    #println(current_node)

    # Raise the current_index
    new_current_index = current_node[1]+1

    # Calculate the options of the current node
    options = DFS_possible_options(new_current_index,lqs_collection,current_node[3])

    # Compute restrictions_dicts of all the options and insert all options_nodes of the current node before the node in the stack
    if length(options) != 0
        if new_current_index == max_depth
            for option in options
                new_lqs_selector = copy(current_node[2])
                push!(new_lqs_selector, [new_current_index, option])
                options_node = [new_current_index, new_lqs_selector,"no restriction_dict"]                                         
                insert!(stack,1,options_node)
            end
        else
            for option in options
                new_lqs_selector = copy(current_node[2])
                push!(new_lqs_selector, [new_current_index, option])
                rest_dict_option = DFS_restrictions_dict(new_current_index,option,hyp_partition_dict,max_depth)
                #println(rest_dict_option)
                new_restrictions_dict = OrderedDict([id=>[vcat(current_node[3][id][1],rest_dict_option[id][1]),
                                                        vcat(current_node[3][id][2],rest_dict_option[id][2])] for id in range(new_current_index+1,max_depth)])
                options_node = [new_current_index,new_lqs_selector,new_restrictions_dict]                                         
                insert!(stack,1,options_node)
            end
        end
    end

    # Remove the current node  and all similar nodes from the stack
    deleteat!(stack,findall(x-> x == current_node,stack))

    # Go recursively through the stack
    for node in stack
        #println(node[1:2])
        if node[1] < max_depth
            DFS_LIFO(node, stack, hyp_partition_dict, lqs_collection, max_depth, result_list, v_results)

        elseif node[1] == max_depth
            if node in v_results
                #println("I'm here")
                continue
            else
                push!(v_results,node)

                # Check the linear-q-subclass selector condition for the current node
                holds = true
                for combi in Oscar.combinations(node[2],2)
                    loop = true
                    inters = intersect(combi[1][2],combi[2][2]) 
                    if  length(inters) != 0
                        u = [combi[1][1],combi[2][1]]
                        for h in inters
                            counter = 0
                            part = hyp_partition_dict[h]
                            for b in part
                                if issubset(u,b)
                                    counter += 1
                                end
                            end
                            if counter == 0
                                loop = false
                                break
                            end
                        end
                    end
                    if loop == false
                        holds = false
                        break
                    end
                end

                # Push current node into the result list if above condition holds
                if holds 
                    push!(result_list, node[2])
                    #deleteat!(stack,findall(x-> x == node,stack))
                end
            end
        end
    end
end
################################################################################

@doc raw"""
    DFS_enum(QM:: Q_Matroid, init_num:: Any, info=false:: Any)

    Inputs a q-matroid `QM` and initial linear q-subclass `init_num`.
    Outputs a list of all possible lqs-selectors.
"""

function DFS_enum(QM:: Q_Matroid, init_num:: Any, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []
    v_results = []
    current_index = 1

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)

    # Define stack shape
    stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

    # Only for test purpose, later maybe replaced by iteration over all possible init choices
    ################################################################################
    # Compute Initial node
    lqs = lqs_collection[init_num]
    lqs_selector = [[current_index, lqs]]
    restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
    init_node = [current_index,lqs_selector,restrictions_dict]

    # Now push the `Init_node` into the stack
    push!(stack,init_node)

    # Start the DFS-Algo
    DFS_LIFO(stack[1], stack, hyp_partition_dict, lqs_collection, max_depth, result_list, v_results)

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end
################################################################################

@doc raw"""
    DFS_enumV2(QM:: Q_Matroid, info=false:: Any)

    Inputs a q-matroid `QM`.
    Outputs a list of all possible lqs-selectors while iteration over a possible init lqs choices.
"""

function DFS_enumV2(QM:: Q_Matroid, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []
    v_results = []

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])
    println("Done computing the hyperplane partitions")

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)
    iter_bound = length(lqs_collection)
    println("Done computing the lqs collection")
    println("Start iteration...")


    # Iterate over all possible initial lqs choices
    ################################################################################
    for i in range(1,iter_bound)

        # Define stack shape and current index
        current_index = 1
        stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

        # Compute Initial node
        lqs = lqs_collection[i]
        lqs_selector = [[current_index, lqs]]
        restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
        init_node = [current_index,lqs_selector,restrictions_dict]

        # Now push the `Init_node` into the stack
        push!(stack,init_node)

        # Start the DFS-Algo
        DFS_LIFO(stack[1], stack, hyp_partition_dict, lqs_collection, max_depth, result_list, v_results)

        # Progress
        println("$i. choice of $iter_bound done")
        println("-------------------------------------")

        # Empty stack
        empty!(stack)
    end

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end

################################################################################
## DPS-Enumeration-Algo for a fixed q-matroid: Iterative approach
################################################################################

@doc raw"""
    Iter_DFS(stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any)

    ....
"""
function Iter_DFS(stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any)
    
    while length(stack)!=0
        current_node = pop!(stack)

        if current_node[1] < max_depth

            # Raise the current_index
            new_current_index = current_node[1]+1

            # Calculate the options of the current node
            options = DFS_possible_options(new_current_index,lqs_collection,current_node[3])

            # Compute restrictions_dicts of all the options and insert all options_nodes of the current node before the node in the stack
            if length(options) != 0
                if new_current_index == max_depth
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        options_node = [new_current_index, new_lqs_selector,"no restriction_dict"]                                         
                        push!(stack,options_node)
                    end
                else
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        rest_dict_option = DFS_restrictions_dict(new_current_index,option,hyp_partition_dict,max_depth)
                        new_restrictions_dict = OrderedDict([id=>[vcat(current_node[3][id][1],rest_dict_option[id][1]),
                                                                vcat(current_node[3][id][2],rest_dict_option[id][2])] for id in range(new_current_index+1,max_depth)])
                        options_node = [new_current_index,new_lqs_selector,new_restrictions_dict]                                         
                        push!(stack,options_node)
                    end
                end
            end

        elseif current_node[1] == max_depth

            # Check the linear-q-subclass selector condition for the current node
            holds = true
            for combi in Oscar.combinations(current_node[2],2)
                loop = true
                inters = intersect(combi[1][2],combi[2][2]) 
                if  length(inters) != 0
                    u = [combi[1][1],combi[2][1]]
                    for h in inters
                        counter = 0
                        part = hyp_partition_dict[h]
                        for b in part
                            if issubset(u,b)
                                counter += 1
                            end
                        end
                        if counter == 0
                            loop = false
                            break
                        end
                    end
                end
                if loop == false
                    holds = false
                    break
                end
            end

            # Push current node into the result list if above condition holds
            if holds 
                push!(result_list, current_node[2])
            end
        end
    end
end
################################################################################

@doc raw"""
    Iter_DFS_enum(QM:: Q_Matroid, init_num:: Any, info=false:: Any)

    Inputs a q-matroid `QM` and initial linear q-subclass `init_num`.
    Outputs a list of all possible lqs-selectors.
"""

function Iter_DFS_enum(QM:: Q_Matroid, init_num:: Any, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []
    current_index = 1

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)

    # Only for test purpose, later maybe replaced by iteration over all possible init choices
    ################################################################################
    # Define stack shape
    stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

    # Compute Initial node
    lqs = lqs_collection[init_num]
    lqs_selector = [[current_index, lqs]]
    restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
    init_node = [current_index,lqs_selector,restrictions_dict]

    # Now push the `Init_node` into the stack
    push!(stack,init_node)

    # Start the DFS-Algo
    Iter_DFS(stack, hyp_partition_dict, lqs_collection, max_depth, result_list)

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end
################################################################################

@doc raw"""
    Iter_DFS_enumV2(QM:: Q_Matroid, info=false:: Any)

    Inputs a q-matroid `QM`.
    Outputs a list of all possible lqs-selectors while iteration over a possible init lqs choices.
"""

function Iter_DFS_enumV2(QM:: Q_Matroid, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])
    println("Done computing the hyperplane partitions")

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)
    iter_bound = length(lqs_collection)
    println("Done computing the lqs collection")
    println("Start iteration...")


    # Iterate over all possible initial lqs choices
    ################################################################################
    for i in range(1,iter_bound)

        # Define stack shape and current index
        current_index = 1
        stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

        # Compute Initial node
        lqs = lqs_collection[i]
        lqs_selector = [[current_index, lqs]]
        restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
        init_node = [current_index,lqs_selector,restrictions_dict]

        # Now push the `Init_node` into the stack
        push!(stack,init_node)

        # Start the DFS-Algo
        Iter_DFS(stack, hyp_partition_dict, lqs_collection, max_depth, result_list)

        # Progress
        println("$i. choice of $iter_bound done")
        println("-------------------------------------")

        # Empty stack
        empty!(stack)
    end

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end

@doc raw"""
    Iter_DFS_enumV3(QM:: Q_Matroid, info=false:: Any)

    Inputs a q-matroid `QM`.
    Outputs a list of all possible lqs-selectors while iteration over a possible init lqs choices.
"""

function Iter_DFS_enumV3(QM:: Q_Matroid, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])
    println("Done computing the hyperplane partitions")

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)
    init_collection = Initial_linear_q_subclasses(hyps,lqs_collection,dim-1,field)
    iter_bound = length(init_collection)
    #iter_bound = length(lqs_collection)
    println("Done computing the lqs collection")
    println("Start iteration...")


    # Iterate over all possible initial lqs choices
    ################################################################################
    for i in range(1,iter_bound)

        # Define stack shape and current index
        current_index = 1
        stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

        # Compute Initial node
        lqs = init_collection[i]
        lqs_selector = [[current_index, lqs]]
        restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
        init_node = [current_index,lqs_selector,restrictions_dict]

        # Now push the `Init_node` into the stack
        push!(stack,init_node)

        # Start the DFS-Algo
        Iter_DFS(stack, hyp_partition_dict, lqs_collection, max_depth, result_list)

        # Progress
        println("$i. choice of $iter_bound done")
        println("-------------------------------------")

        # Empty stack
        empty!(stack)
    end

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end

################################################################################
## DPS-Enumeration-Algo for a fixed q-matroid: Iterative iso free approach
################################################################################

@doc raw"""
    LqS_selector_to_bases(lqs_selector:: Any, ones_dict:: Any, indeps::Any, emb_bases::Any, qrankm1_subs:: Any)

    ....   
"""

function  LqS_selector_to_bases(lqs_selector:: Any, ones_dict:: Any, indeps::Any, emb_bases::Any, qrankm1_subs:: Any)
    ext_bases = [x for x in emb_bases]
    
    for elm in lqs_selector
        all_subs = []
        for h in elm[2]
            subs = reduce(vcat,subspaces_fix_space(h))
            #println(subs)
            inters = intersect(subs,qrankm1_subs)
            union!(all_subs,inters)
            #= for x in inters
                push!(all_subs,x)
            end =#
        end
        #println(all_subs)

        for x in indeps
            #println(!(x[1] in all_subs))
            if !(x[1] in all_subs)
                sum = sum_vsV2(x[2],ones_dict[elm[1]])
                push!(ext_bases,sum)
            end
        end
    end

    return unique!(ext_bases)

end
################################################################################

@doc raw"""
    Isofree_DFS(stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any,
                    ones_dict::Any, qrank_subs::Any, qrankm1_subs:: Any, bases:: Any, Indeps::Any, Stab::Any)

    ....
"""
function Isofree_DFS(stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any, result_list::Any,
                    ones_dict::Any, qrank_subs::Any, qrankm1_subs:: Any, emb_bases:: Any, indeps::Any, act_fn, Stab::Any)
    
    while length(stack)!=0
        current_node = pop!(stack)

        if current_node[1] < max_depth

            # Raise the current_index
            new_current_index = current_node[1]+1

            # Calculate the options of the current node
            options = DFS_possible_options(new_current_index,lqs_collection,current_node[3])

            # Compute restrictions_dicts of all the options and insert all options_nodes of the current node before the node in the stack
            if length(options) != 0
                if new_current_index == max_depth
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        options_node = [new_current_index, new_lqs_selector,"no restriction_dict"]                                         
                        push!(stack,options_node)
                    end
                else
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        rest_dict_option = DFS_restrictions_dict(new_current_index,option,hyp_partition_dict,max_depth)
                        new_restrictions_dict = OrderedDict([id=>[vcat(current_node[3][id][1],rest_dict_option[id][1]),
                                                                vcat(current_node[3][id][2],rest_dict_option[id][2])] for id in range(new_current_index+1,max_depth)])
                        options_node = [new_current_index,new_lqs_selector,new_restrictions_dict]                                         
                        push!(stack,options_node)
                    end
                end
            end

        elseif current_node[1] == max_depth

            # Check the linear-q-subclass selector condition for the current node
            holds = true
            for combi in Oscar.combinations(current_node[2],2)
                loop = true
                inters = intersect(combi[1][2],combi[2][2]) 
                if  length(inters) != 0
                    u = [combi[1][1],combi[2][1]]
                    for h in inters
                        counter = 0
                        part = hyp_partition_dict[h]
                        for b in part
                            if issubset(u,b)
                                counter += 1
                            end
                        end
                        if counter == 0
                            loop = false
                            break
                        end
                    end
                end
                if loop == false
                    holds = false
                    break
                end
            end

            # Push current node into the result list if above condition holds and its a is in canonical form
            if holds
                lqss_bases = LqS_selector_to_bases(current_node[2],ones_dict,indeps,emb_bases,qrankm1_subs)
                #println(lqss_bases)
                set_lqss_bases = Set(lqss_bases)
                enc_lqss_bases = Q_Matroid_base_enc(lqss_bases, qrank_subs)
                orb = []
                for G in Stab
                    b_set = act_fn(set_lqss_bases,G)
                    new_b = [x for x in b_set]
                    enc_new_b = Q_Matroid_base_enc(new_b, qrank_subs)
                    push!(orb,enc_new_b)
                end
                sort!(orb)

                if enc_lqss_bases == orb[1]
                    push!(result_list, [current_node[2], lqss_bases, enc_lqss_bases])
                end
            end
        end
    end
end
################################################################################

@doc raw"""
    Isofree_DFS_enum(QM:: Q_Matroid, info=false:: Any)

    Inputs a q-matroid `QM`.
    Outputs a list of all possible non-isomorphic lqs-selectors while iteration over a possible init lqs choices.
"""

function Isofree_DFS_enum(QM:: Q_Matroid, info=false:: Any)
    # Define all necessary variables
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []

    # Compute the bases, (rank-1)-dim. independent spaces and embed them
    O_bases = QM.bases
    q_rank = rank(O_bases[1])
    qrankm1_subs = subspaces_fix_dim(field,q_rank-1,dim-1)
    #println(qrankm1_subs)
    O_indeps = intersect(Q_Matroid_Independentspaces(QM),qrankm1_subs)
    emb_bases = standard_embedding_higher_dimV2(O_bases,dim)
    indeps = [[I,standard_embedding_higher_dimV2([I],dim)[1]] for I in O_indeps]
    #bases = [O_bases,emb_bases]

    # Compute all q_rank spaces and order them
    qrank_subs = subspaces_fix_dim(field, q_rank, dim)
    #sort!(qrank_subs; lt = Lex_compare_subs)

    # Compute the Stabilizer of the embed bases
    GLn = Oscar.general_linear_group(dim, field)
    emb_bases_set = Set(emb_bases)
    actfn = function(spaces,G)
        return Set([rref(C*matrix(G))[2] for C in spaces])
    end
    S, emb = stabilizer(GLn, emb_bases_set, actfn)
    println("Done computing the stabilizer")

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])
    println("Done computing the hyperplane partitions")

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_q_subclasses(QM, hyps)
    init_collection = Initial_linear_q_subclasses(hyps,lqs_collection,dim-1,field)
    iter_bound = length(init_collection)
    #iter_bound = length(lqs_collection)
    println("Done computing the lqs collection")
    println("Start iteration...")


    # Iterate over all possible initial lqs choices
    ################################################################################
    for i in range(1,iter_bound)

        # Define stack shape and current index
        current_index = 1
        stack = [] # stack_elements: [current_index, lqs_selector, restrictions_dict]

        # Compute Initial node
        lqs = init_collection[i]
        lqs_selector = [[current_index, lqs]]
        restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
        init_node = [current_index,lqs_selector,restrictions_dict]

        # Now push the `Init_node` into the stack
        push!(stack,init_node)

        # Start the DFS-Algo
        Isofree_DFS(stack, hyp_partition_dict, lqs_collection, max_depth, result_list, ones_dict, qrank_subs, qrankm1_subs, emb_bases, indeps, actfn, S)

        # Progress
        println("$i. choice of $iter_bound done")
        println("-------------------------------------")

        # Empty stack
        empty!(stack)
    end

    if info
        return unique!(result_list), hyps, ones_dict
    elseif info == false
        return unique!(result_list)
    end
    ################################################################################

end


################################################################################
## Translate LqS to q-matroid
################################################################################

@doc raw"""
    LqS_selector_to_q_matroid(QM:: Q_Matroid,  fs::Any, hs:: Any, lqs_selector:: Any, ones_dict:: Any, info=false:: Any)

    Inputs the initial q-matroid `QM`, its flats, its hyperplanes and a `lqs_selector`,  an constructs the corresponding 1-dim. extension.
    We directly build the set of hyperplanes of the 1-dim. extension from the `lqs_selector`.   
"""

function LqS_selector_to_q_matroid(QM:: Q_Matroid, fs::Any, hs:: Any, lqs_selector:: Any, ones_dict:: Any, info=false:: Any)
    groundspace = QM.groundspace
    dim = ncols(groundspace)+1
    extension_hyps = []
    u_all_lqs_hyps = []

    # Rank of q-matroid
    if length(QM.bases)!= 0
        q_rank = rank(QM.bases[1])
    else
        q_rank = 0
    end

    # Indeps and deps for rank computation
    indeps = Q_Matroid_Independentspaces(QM)
    deps = Q_Matroid_Dependentspaces(QM)

    # Compute corank 2 flats
    corank2_fs = [f for f in fs if Q_Matroid_Ranks(QM,f,indeps,deps) == q_rank-2]

    # Set 1: ⋃_{e}{ H+e | H ∈ μ'(e)}
    # Set 3: { F+e | F corank 2 flat s.t. F\not≤ H for all H ∈ μ^'(e)}
    for elm in lqs_selector
        # Collect all appearing lqs hyperplanes
        for h in elm[2]
            push!(u_all_lqs_hyps,h)
        end
        
        # Set 1: computation
        if length(elm[2]) != 0
            emb_col = standard_embedding_higher_dimV2(elm[2],dim)
            for space in emb_col
                sum = sum_vsV2(space,ones_dict[elm[1]])
                push!(extension_hyps,sum)
            end
        end

        # Set 3: computation
        for f in corank2_fs
            superhyps = intersect(containments_fix_spaceV2(f),hs)
            if length(intersect(superhyps,elm[2])) == 0 
                emb_f = standard_embedding_higher_dimV2([f],dim)[1]
                sum = sum_vsV2(emb_f, ones_dict[elm[1]])
                push!(extension_hyps,sum)
            end
        end

    end

    # Set 2: { H | H ̸∈ μ'(e) for all e}
    u_all_lqs_hyps = unique(u_all_lqs_hyps)
    for h in hs
        if !(h in u_all_lqs_hyps)
            push!(extension_hyps,standard_embedding_higher_dimV2([h],dim)[1])
        end
    end
    
    extension_hyps = unique(extension_hyps)

    # Convert into q-matroid
    if length(extension_hyps) == 0
        field = base_ring(groundspace)
        Ext_QM = Uniform_q_matroid(field,0,dim)
    else
        Ext_QM = q_matroid_from_hyperplanes(extension_hyps)
    end

    if info 
        return Ext_QM, extension_hyps
    elseif  info == false
        return Ext_QM
    end 

end

@doc raw"""
    LqS_selector_to_q_matroidV2(QM:: Q_Matroid,  corank2_fs::Any, hs:: Any, lqs_selector:: Any, ones_dict:: Any, info=false:: Any)

    Inputs the initial q-matroid `QM`, its corank 2 flats, its hyperplanes and a `lqs_selector`,  an constructs the corresponding 1-dim. extension.
    We directly build the set of hyperplanes of the 1-dim. extension from the `lqs_selector`.   
"""

function LqS_selector_to_q_matroidV2(QM:: Q_Matroid, corank2_fs::Any, hs:: Any, lqs_selector:: Any, ones_dict:: Any, info=false:: Any)
    groundspace = QM.groundspace
    dim = ncols(groundspace)+1
    extension_hyps = []
    u_all_lqs_hyps = []

    # Rank of q-matroid
    if length(QM.bases)!= 0
        q_rank = rank(QM.bases[1])
    else
        q_rank = 0
    end

    #= # Indeps and deps for rank computation
    indeps = Q_Matroid_Independentspaces(QM)
    deps = Q_Matroid_Dependentspaces(QM)

    # Compute corank 2 flats
    corank2_fs = [f for f in fs if Q_Matroid_Ranks(QM,f,indeps,deps) == q_rank-2] =#

    # Set 1: ⋃_{e}{ H+e | H ∈ μ'(e)}
    # Set 3: { F+e | F corank 2 flat s.t. F\not≤ H for all H ∈ μ^'(e)}
    for elm in lqs_selector
        # Collect all appearing lqs hyperplanes
        for h in elm[2]
            push!(u_all_lqs_hyps,h)
        end
        
        # Set 1: computation
        if length(elm[2]) != 0
            emb_col = standard_embedding_higher_dimV2(elm[2],dim)
            for space in emb_col
                sum = sum_vsV2(space,ones_dict[elm[1]])
                push!(extension_hyps,sum)
            end
        end

        # Set 3: computation
        for f in corank2_fs
            superhyps = intersect(containments_fix_spaceV2(f),hs)
            if length(intersect(superhyps,elm[2])) == 0 
                emb_f = standard_embedding_higher_dimV2([f],dim)[1]
                sum = sum_vsV2(emb_f, ones_dict[elm[1]])
                push!(extension_hyps,sum)
            end
        end

    end

    # Set 2: { H | H ̸∈ μ'(e) for all e}
    u_all_lqs_hyps = unique(u_all_lqs_hyps)
    for h in hs
        if !(h in u_all_lqs_hyps)
            push!(extension_hyps,standard_embedding_higher_dimV2([h],dim)[1])
        end
    end
    
    extension_hyps = unique(extension_hyps)

    # Convert into q-matroid
    if length(extension_hyps) == 0
        field = base_ring(groundspace)
        Ext_QM = Uniform_q_matroid(field,0,dim)
    else
        Ext_QM = q_matroid_from_hyperplanes(extension_hyps)
    end

    if info 
        return Ext_QM, extension_hyps
    elseif  info == false
        return Ext_QM
    end 

end
################################################################################

@doc raw"""
    Q_Matroid_Corank2Flats(QM:: Q_Matroid)

    Computes the corank 2 flats of the q-matroid `QM`.   
"""

function Q_Matroid_Corank2Flats(QM:: Q_Matroid)

    # Rank of q-matroid
    if length(QM.bases)!= 0
        q_rank = rank(QM.bases[1])
    else
        q_rank = 0
    end

    # Indeps and deps for rank computation
    indeps = Q_Matroid_Independentspaces(QM)
    deps = Q_Matroid_Dependentspaces(QM)
    flats = Q_Matroid_Flats(QM)

    # Return corank 2 flats
    return [f for f in flats if Q_Matroid_Ranks(QM,f,indeps,deps) == q_rank-2]

end
################################################################################
