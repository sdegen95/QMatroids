################################################################################
##  Enumeration of q-matroids
################################################################################
using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices
include("./helper_functions.jl")


@doc raw"""
    Diamond_prop(indeps::AbstractVector{fpMatrix}, deps::AbstractVector{fpMatrix}, all_diams=nothing::Union{Nothing,AbstractVector{AbstractVector{fpMatrix}}})

    Returns if the union list of `indeps` and `deps` satisfies the q-matroid diamond condtion.

    For the `all_diams`-option one can insert a list of all diamonds of the ambient space.

    Note: This is required to speed up the computations in the below enumeration functions.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function Diamond_prop(indeps::AbstractVector{fpMatrix}, deps::AbstractVector{fpMatrix}, all_diams=nothing::Union{Nothing,AbstractVector{AbstractVector{fpMatrix}}})
    holds = true

    # Put all current spaces together in one list
    all_current_spaces = union(indeps,deps)
    
    # Sort them w.r.t to their subspace dimension
    sort!(all_current_spaces, by = x -> rank(x))

    # Create all possible diamonds
    if isnothing(all_diams)
        diams = diamond_list(all_current_spaces)
    else
        # Here we put in all possible diamonds of the vector_space, not only those in the current spaces
        # Check which of all the diamonds of the v.s. is in the current_spaces_list
        diams = []
        for elm in all_diams
            if issubset(elm,all_current_spaces)
                push!(diams,elm)
            end
        end
    end

    # Check if all currently possible diamonds satisfy the one of the four possible options
    for diam in diams
        sort!(diam, by = x -> rank(x))
        overall_count = 0
        if diam[1] in indeps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in deps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in deps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                elseif elm == diam[length(diam)]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # mixed diamond
            count = 0
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in indeps
                        continue
                    elseif elm in deps
                        count += 1
                    end
                elseif elm == diam[length(diam)]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
                if count > 1
                    overall_count += 1
                    break
                end
            end

        elseif diam[1] in deps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # mixed diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count +=1
                        break
                    else
                        continue
                    end
                end
            end
        end

        if overall_count >= 4
            holds = false
            break
        else
            continue
        end
    end

    
    return holds
end

################################################################################
# Enumeration dimension 3 (rank 2)
################################################################################


@doc raw"""
    
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function Dim3_create_neighbors(indeps::AbstractVector{fpMatrix},deps::AbstractVector{fpMatrix},counter::Oscar.IntegerUnion,lo_dict::AbstractDict,all_diams::AbstractVector{AbstractVector{fpMatrix}})
    field = base_ring(indeps[1])
    complement_list = []
    new_counter = counter + 1

    # Get the space which are not assigned yet
    considered_spaces = collect(values(lo_dict))[new_counter][2]
    for space in considered_spaces
        if !(space in indeps)
            if !(space in deps)
                push!(complement_list,space)
            end
        end
    end

    # List all the two spaces containing the current one-space
    two_spaces_containment = []
    for sub in collect(values(lo_dict))[new_counter][2]
        if rank(sub)==2
            push!(two_spaces_containment,sub)
        end
    end

    # Get the one two space which is already assigned
    two_spaces_not_complement = []
    for space in two_spaces_containment
        if !(space in complement_list)
            push!(two_spaces_not_complement,space)
        end
    end

    # Compute intersection with dep spaces
    inters = intersect(two_spaces_not_complement,deps)

    # Decide the possible options: we have 3 option of 2-dim q-matroids
    options = [] 
    option_num = 3
    for i in range(1,option_num)
    # 1. options: choose one of the two-spaces in the complement_list as dependent
        if i == 1
            if two_spaces_not_complement != []
                if !(two_spaces_not_complement[1] in deps)
                    for space_1 in complement_list
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        push!(new_deps_list,space_1)
                        for space_2 in complement_list
                            if space_2 != space_1
                                push!(new_indeps_list,space_2)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    end
                end
            else
                for space_1 in complement_list
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    push!(new_deps_list,space_1)
                    for space_2 in complement_list
                        if space_2 != space_1
                            push!(new_indeps_list,space_2)
                        end
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end
    # 2. options: choose one of the two-spaces which is already dependent as dependent
        elseif i == 2
            if inters != []
                for space_1 in inters
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space_2 in complement_list
                        push!(new_indeps_list,space_2)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end

    # 3. options: choose none of the two-spaces in the list as dependent
        elseif i == 3
            if two_spaces_containment != []
                right_count = 0
                for space in two_spaces_containment
                    if space in indeps
                        right_count += 1 
                    elseif space in complement_list
                        right_count += 1
                    else
                        continue
                    end
                end

                if right_count == q_binomcoeff(Int(characteristic(field)),3-1,2-1)
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space in complement_list
                        push!(new_indeps_list,space)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                else
                    continue
                end
            end
        end
    end

    return options
end

function Dim3_LIFO(current_node::AbstractVector,stack::AbstractVector,lo_dict::AbstractDict,result_list::AbstractVector,all_diams::AbstractVector{AbstractVector{fpMatrix}},num_all_subs::Oscar.IntegerUnion,num_leftovers::Oscar.IntegerUnion)
    # Calculate the neighbors of the current node
    neighbors = Dim3_create_neighbors(current_node[1],current_node[2],current_node[3],lo_dict,all_diams)

    # Insert all neigbours of the current node before the node in the stack list
    if length(neighbors) != 0
        for neighbor in neighbors
            insert!(stack,1,neighbor)
        end
    end

    # Remove the current node from the stack
    deleteat!(stack,findall(x-> x == current_node,stack))

    # Gone recursivly through the stack
    for node in stack
        #println(node)
        if node[3] < num_leftovers && length(node[1]) + length(node[2]) < num_all_subs
            Dim3_LIFO(node,stack,lo_dict,result_list,all_diams,num_all_subs,num_leftovers)

        elseif node[3] == num_leftovers || length(node[1]) + length(node[2]) == num_all_subs
            #println("i'm here")
            push!(result_list,[node[1],node[2],q_matroid_from_independentspaces(node[1],true)])
        end
    end

end

function Dim3_q_matroid_DFS(QM::Q_Matroid)
    Field = base_ring(QM.groundspace)
    Init_Indeps = Q_Matroid_Independentspaces(QM)
    Init_Deps = Q_Matroid_Dependentspaces(QM)

    Trans_Indeps = standard_embedding_higher_dim(Init_Indeps,3)

    if Init_Deps != []
        Trans_Deps = standard_embedding_higher_dim(Init_Deps,3)
    else
        Trans_Deps = AbstractVector{fpMatrix}([])
    end

    Indeps_list = AbstractVector{fpMatrix}([])
    Deps_list = AbstractVector{fpMatrix}([])
    stack = []
    result_list = []
    LO_dict = OrderedDict([])
    counter = 0


    # First put all indeps and deps of the init_choice in the list
    for indep_spaces in Trans_Indeps
        push!(Indeps_list,indep_spaces)
    end
    for dep_spaces in Trans_Deps
        push!(Deps_list,dep_spaces)
    end

    # Create all diamonds of the vectorspace
    all_subs = all_subspaces(Field,3)
    Num_all_subs = length(all_subs)
    all_diams = diamond_list(all_subs)

    # Now we create a dictionary with the leftover 1-spaces
    one_spaces = subspaces_fix_dim(Field,1,3)
    index = 1
    for space in one_spaces
        if !(space in Indeps_list)
            if !(space in Deps_list)
                merge!(LO_dict,Dict(index=>[space,containments_fix_space(space)]))
                index += 1
            end
        end
    end
    Num_leftovers = length(collect(values(LO_dict)))

    # Push the id_mat into Deps_list
    id_mat = subspaces_fix_dim(Field,3,3)[1]
    push!(Deps_list,id_mat)

    # Push all LO-one-space in Indeps_list
    for value in values(LO_dict)
        push!(Indeps_list,value[1])
    end

    # Looking for a loop in the init_choice, so all it's two spaces are also dependent
    for space in Deps_list
        if rank(space) == 1
            contained_in = containments_fix_space(space)
            for sub in contained_in
                if rank(sub) == 2
                    if !(sub in Deps_list) && !(sub in Indeps_list)
                        push!(Deps_list,sub)
                    end
                end
            end
        end
    end

    # Now push the Tuple [Indeps_list,Deps_list] into the stack
    push!(stack,[Indeps_list,Deps_list,counter])

    # Create the intial neighbors and start DFS-Algo
    Dim3_LIFO(stack[1],stack,LO_dict,result_list,all_diams,Num_all_subs,Num_leftovers)

    return unique!(result_list)
end

################################################################################
# Enumeration dimension 4 (rank 2)
################################################################################


@doc raw"""
    
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function Dim4_create_neighbors(indeps::AbstractVector{fpMatrix},deps::AbstractVector{fpMatrix},counter::Oscar.IntegerUnion,lo_dict::AbstractDict,all_diams::AbstractVector{AbstractVector{fpMatrix}})
    field = base_ring(indeps[1])
    complement_list = []
    new_counter = counter + 1

    # Get the space which are not assigned yet
    considered_spaces = collect(values(lo_dict))[new_counter][2]
    for space in considered_spaces
        if !(space in indeps)
            if !(space in deps)
                push!(complement_list,space)
            end
        end
    end
    
    # Get all diams contained in the considered_spaces with out the whole space
    considered_diams = []
    new_cons_spaces = sort([x for x in considered_spaces if rank(x)!=4],by = y->rank(y))
    for elm in all_diams
        if issubset(elm,new_cons_spaces)
            push!(considered_diams,elm)
        end
    end


    # List all the two spaces containing the current one-space
    two_spaces_containment = []
    for sub in collect(values(lo_dict))[new_counter][2]
        if rank(sub)==2
            push!(two_spaces_containment,sub)
        end
    end

    # Get the one two space which is already assigned
    two_spaces_not_complement = []
    for space in two_spaces_containment
        if !(space in complement_list)
            push!(two_spaces_not_complement,space)
        end
    end

    # Compute intersection with dep spaces
    inters = intersect(two_spaces_not_complement,deps)

    # Decide the possible options: we have 3 option of 2-dim q-matroids
    options = [] 
    option_num = 4
    for i in range(1,option_num)
    # 1. options: choose one of the two-spaces in the complement_list as dependent
        if i == 1
            if two_spaces_not_complement != []
                if !(two_spaces_not_complement[1] in deps)
                    for space_1 in complement_list
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        push!(new_deps_list,space_1)
                        for space_2 in complement_list
                            if space_2 != space_1
                                push!(new_indeps_list,space_2)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    end
                end
            else
                for space_1 in complement_list
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    push!(new_deps_list,space_1)
                    for space_2 in complement_list
                        if space_2 != space_1
                            push!(new_indeps_list,space_2)
                        end
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end
    # 2. options: choose one of the two-spaces which is already dependent as dependent
        elseif i == 2
            if inters != []
                for space_1 in inters
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space_2 in complement_list
                        push!(new_indeps_list,space_2)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end

    # 3. options: choose none of the two-spaces in the list as dependent
        elseif i == 3
            if two_spaces_containment != []
                right_count = 0
                for space in two_spaces_containment
                    if space in indeps
                        right_count += 1 
                    elseif space in complement_list
                        right_count += 1
                    else
                        continue
                    end
                end

                if right_count == q_binomcoeff(Int(characteristic(field)),4-1,2-1)
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space in complement_list
                        push!(new_indeps_list,space)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                else
                    continue
                end
            end

    # 4. options: Choose three 2-spaces as dependent, which are all contained in one 3-space
        elseif i == 4
            if considered_diams != []
                for diam in considered_diams
                    sort!(diam,by = x->rank(x))
                    twos = []
                    for elm in diam
                        if rank(elm)==2
                            push!(twos,elm)
                        end
                    end
                    if issubset(twos,complement_list)
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            push!(new_deps_list,elm)
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    elseif intersect(twos,deps) != []
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            if !(elm in deps)
                                push!(new_deps_list,elm)
                            end
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    else
                        continue
                    end
                end
            end
        end
    end

    return options
end

function Dim4_LIFO(current_node::AbstractVector,stack::AbstractVector,lo_dict::AbstractDict,result_list::AbstractVector,all_diams::AbstractVector{AbstractVector{fpMatrix}},num_all_subs::Oscar.IntegerUnion,num_leftovers::Oscar.IntegerUnion)
    # Calculate the neighbors of the current node
    neighbors = Dim4_create_neighbors(current_node[1],current_node[2],current_node[3],lo_dict,all_diams)

    # Insert all neigbours of the current node before the node in the stack list
    if length(neighbors) != 0
        for neighbor in neighbors
            insert!(stack,1,neighbor)
        end
    end

    # Remove the current node from the stack
    deleteat!(stack,findall(x-> x == current_node,stack))

    # Gone recursivly through the stack
    for node in stack
        #println(node)
        if node[3] < num_leftovers && length(node[1]) + length(node[2]) < num_all_subs
            Dim4_LIFO(node,stack,lo_dict,result_list,all_diams,num_all_subs,num_leftovers)

        elseif node[3] == num_leftovers || length(node[1]) + length(node[2]) == num_all_subs
            #println("i'm here")
            push!(result_list,[node[1],node[2],q_matroid_from_independentspaces(node[1],true)])
        end
    end

end

function Dim4_q_matroid_DFS(QM::Q_Matroid)
    Field = base_ring(QM.groundspace)
    Init_Indeps = Q_Matroid_Independentspaces(QM)
    Init_Deps = Q_Matroid_Dependentspaces(QM)

    Trans_Indeps = standard_embedding_higher_dim(Init_Indeps,4)

    if Init_Deps != []
        Trans_Deps = standard_embedding_higher_dim(Init_Deps,4)
    else
        Trans_Deps = AbstractVector{fpMatrix}([])
    end

    Indeps_list = AbstractVector{fpMatrix}([])
    Deps_list = AbstractVector{fpMatrix}([])
    stack = []
    result_list = []
    LO_dict = OrderedDict([])
    counter = 0


    # First put all indeps and deps of the init_choice in the list
    for indep_spaces in Trans_Indeps
        push!(Indeps_list,indep_spaces)
    end
    for dep_spaces in Trans_Deps
        push!(Deps_list,dep_spaces)
    end

    # Create all diamonds of the vectorspace
    all_subs = all_subspaces(Field,4)
    Num_all_subs = length(all_subs)
    all_diams = diamond_list(all_subs)

    # Now we create a dictionary with the leftover 1-spaces
    one_spaces = subspaces_fix_dim(Field,1,4)
    index = 1
    for space in one_spaces
        if !(space in Indeps_list)
            if !(space in Deps_list)
                merge!(LO_dict,Dict(index=>[space,containments_fix_space(space)]))
                index += 1
            end
        end
    end
    Num_leftovers = length(collect(values(LO_dict)))

    # Push the id_mat into Deps_list
    id_mat = subspaces_fix_dim(Field,4,4)[1]
    push!(Deps_list,id_mat)

    # Push all 3-spaces in Deps_list
    three_spaces = subspaces_fix_dim(Field,3,4)
    for space in three_spaces
        if !(space in Deps_list)
            push!(Deps_list,space)
        end
    end

    # Push all LO-one-space in Indeps_list
    for value in values(LO_dict)
        push!(Indeps_list,value[1])
    end

    # Looking for a loop in the init_choice, so all it's two spaces are also dependent
    for space in Deps_list
        if rank(space) == 1
            contained_in = containments_fix_space(space)
            for sub in contained_in
                if rank(sub) == 2
                    if !(sub in Deps_list) && !(sub in Indeps_list)
                        push!(Deps_list,sub)
                    end
                end
            end
        end
    end

    # Now push the Tuple [Indeps_list,Deps_list] into the stack
    push!(stack,[Indeps_list,Deps_list,counter])

    # Create the intial neighbors and start DFS-Algo
    Dim4_LIFO(stack[1],stack,LO_dict,result_list,all_diams,Num_all_subs,Num_leftovers)

    return unique!(result_list)
end

################################################################################
# Enumeration dimension 5 (rank 2)
################################################################################


@doc raw"""
    
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function Dim5_create_neighbors(indeps::AbstractVector{fpMatrix},deps::AbstractVector{fpMatrix},counter::Oscar.IntegerUnion,lo_dict::AbstractDict,all_diams::AbstractVector{AbstractVector{fpMatrix}})
    field = base_ring(indeps[1])
    complement_list = []
    new_counter = counter + 1

    # Get the space which are not assigned yet
    considered_spaces = collect(values(lo_dict))[new_counter][2]
    for space in considered_spaces
        if !(space in indeps)
            if !(space in deps)
                push!(complement_list,space)
            end
        end
    end
    
    # Get all diams contained in the considered_spaces with out the whole space
    considered_diams = []
    new_cons_spaces = sort([x for x in considered_spaces if rank(x)!=4],by = y->rank(y))
    for elm in all_diams
        if issubset(elm,new_cons_spaces)
            push!(considered_diams,elm)
        end
    end

    # Get all 3-intervals contained in the considered_spaces with out the whole space
    new_cons_spaces2 = sort([x for x in considered_spaces if rank(x)!=5],by = y->rank(y))
    considered_3_ints = k_interval(new_cons_spaces2,3)
    
    # List all the two spaces containing the current one-space
    two_spaces_containment = []
    for sub in collect(values(lo_dict))[new_counter][2]
        if rank(sub)==2
            push!(two_spaces_containment,sub)
        end
    end

    # Get the one two space which is already assigned
    two_spaces_not_complement = []
    for space in two_spaces_containment
        if !(space in complement_list)
            push!(two_spaces_not_complement,space)
        end
    end

    # Compute intersection with dep spaces
    inters = intersect(two_spaces_not_complement,deps)

    # Decide the possible options: we have 3 option of 2-dim q-matroids
    options = [] 
    option_num = 5
    for i in range(1,option_num)
    # 1. options: choose one of the two-spaces in the complement_list as dependent
        if i == 1
            if two_spaces_not_complement != []
                if !(two_spaces_not_complement[1] in deps)
                    for space_1 in complement_list
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        push!(new_deps_list,space_1)
                        for space_2 in complement_list
                            if space_2 != space_1
                                push!(new_indeps_list,space_2)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    end
                end
            else
                for space_1 in complement_list
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    push!(new_deps_list,space_1)
                    for space_2 in complement_list
                        if space_2 != space_1
                            push!(new_indeps_list,space_2)
                        end
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end
    # 2. options: choose one of the two-spaces which is already dependent as dependent
        elseif i == 2
            if inters != []
                for space_1 in inters
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space_2 in complement_list
                        push!(new_indeps_list,space_2)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                end
            end

    # 3. options: choose none of the two-spaces in the list as dependent
        elseif i == 3
            if two_spaces_containment != []
                right_count = 0
                for space in two_spaces_containment
                    if space in indeps
                        right_count += 1 
                    elseif space in complement_list
                        right_count += 1
                    else
                        continue
                    end
                end

                if right_count == q_binomcoeff(Int(characteristic(field)),5-1,2-1)
                    new_indeps_list = copy(indeps)
                    new_deps_list = copy(deps)
                    for space in complement_list
                        push!(new_indeps_list,space)
                    end
                    if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                        push!(options,[new_indeps_list,new_deps_list,new_counter])
                    end
                else
                    continue
                end
            end

    # 4. options: Choose three 2-spaces as dependent, which are all contained in one 3-space
        elseif i == 4
            if considered_diams != []
                for diam in considered_diams
                    sort!(diam,by = x->rank(x))
                    twos = []
                    for elm in diam
                        if rank(elm)==2
                            push!(twos,elm)
                        end
                    end
                    if issubset(twos,complement_list)
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            push!(new_deps_list,elm)
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    elseif intersect(twos,deps) != []
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            if !(elm in deps)
                                push!(new_deps_list,elm)
                            end
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    else
                        continue
                    end
                end
            end

    # 5. options: Choose three 2-spaces as dependent, which are all contained in one 3-space     
        elseif i == 5
            if considered_3_ints != []
                for int in considered_3_ints
                    sort!(int,by = x->rank(x))
                    twos = []
                    for elm in int
                        if rank(elm)==2
                            push!(twos,elm)
                        end
                    end
                    if issubset(twos,complement_list)
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            push!(new_deps_list,elm)
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    elseif intersect(twos,deps) != []
                        new_indeps_list = copy(indeps)
                        new_deps_list = copy(deps)
                        for elm in twos
                            if !(elm in deps)
                                push!(new_deps_list,elm)
                            end
                        end
                        for space in complement_list
                            if !(space in twos)
                                push!(new_indeps_list,space)
                            end
                        end
                        if Diamond_prop(new_indeps_list,new_deps_list,all_diams)
                            push!(options,[new_indeps_list,new_deps_list,new_counter])
                        end
                    else
                        continue
                    end
                end
            end
        end   
    end

    return options
end

function Dim5_LIFO(current_node::AbstractVector,stack::AbstractVector,lo_dict::AbstractDict,result_list::AbstractVector,all_diams::AbstractVector{AbstractVector{fpMatrix}},num_all_subs::Oscar.IntegerUnion,num_leftovers::Oscar.IntegerUnion)
    # Calculate the neighbors of the current node
    neighbors = Dim5_create_neighbors(current_node[1],current_node[2],current_node[3],lo_dict,all_diams)

    # Insert all neigbours of the current node before the node in the stack list
    if length(neighbors) != 0
        for neighbor in neighbors
            insert!(stack,1,neighbor)
        end
    end

    # Remove the current node from the stack
    deleteat!(stack,findall(x-> x == current_node,stack))

    # Gone recursivly through the stack
    for node in stack
        #println(node)
        if node[3] < num_leftovers && length(node[1]) + length(node[2]) < num_all_subs
            Dim5_LIFO(node,stack,lo_dict,result_list,all_diams,num_all_subs,num_leftovers)

        elseif node[3] == num_leftovers || length(node[1]) + length(node[2]) == num_all_subs
            #println("i'm here")
            push!(result_list,[node[1],node[2],q_matroid_from_independentspaces(node[1],true)])
        end
    end

end

function Dim5_q_matroid_DFS(QM::Q_Matroid)
    Field = base_ring(QM.groundspace)
    Init_Indeps = Q_Matroid_Independentspaces(QM)
    Init_Deps = Q_Matroid_Dependentspaces(QM)

    Trans_Indeps = standard_embedding_higher_dim(Init_Indeps,5)

    if Init_Deps != []
        Trans_Deps = standard_embedding_higher_dim(Init_Deps,5)
    else
        Trans_Deps = AbstractVector{fpMatrix}([])
    end

    Indeps_list = AbstractVector{fpMatrix}([])
    Deps_list = AbstractVector{fpMatrix}([])
    stack = []
    result_list = []
    LO_dict = OrderedDict([])
    counter = 0


    # First put all indeps and deps of the init_choice in the list
    for indep_spaces in Trans_Indeps
        push!(Indeps_list,indep_spaces)
    end
    for dep_spaces in Trans_Deps
        push!(Deps_list,dep_spaces)
    end

    # Create all diamonds of the vectorspace
    all_subs = all_subspaces(Field,5)
    Num_all_subs = length(all_subs)
    all_diams = diamond_list(all_subs)

    # Now we create a dictionary with the leftover 1-spaces
    one_spaces = subspaces_fix_dim(Field,1,5)
    index = 1
    for space in one_spaces
        if !(space in Indeps_list)
            if !(space in Deps_list)
                merge!(LO_dict,Dict(index=>[space,containments_fix_space(space)]))
                index += 1
            end
        end
    end
    Num_leftovers = length(collect(values(LO_dict)))

    # Push the id_mat into Deps_list
    id_mat = subspaces_fix_dim(Field,5,5)[1]
    push!(Deps_list,id_mat)

    # Push all 3-spaces in Deps_list
    three_spaces = subspaces_fix_dim(Field,3,5)
    for space in three_spaces
        if !(space in Deps_list)
            push!(Deps_list,space)
        end
    end

    # Push all 3-spaces in Deps_list
    four_spaces = subspaces_fix_dim(Field,4,5)
    for space in four_spaces
        if !(space in Deps_list)
            push!(Deps_list,space)
        end
    end

    # Push all LO-one-space in Indeps_list
    for value in values(LO_dict)
        push!(Indeps_list,value[1])
    end

    # Looking for a loop in the init_choice, so all it's two spaces are also dependent
    for space in Deps_list
        if rank(space) == 1
            contained_in = containments_fix_space(space)
            for sub in contained_in
                if rank(sub) == 2
                    if !(sub in Deps_list) && !(sub in Indeps_list)
                        push!(Deps_list,sub)
                    end
                end
            end
        end
    end

    # Now push the Tuple [Indeps_list,Deps_list] into the stack
    push!(stack,[Indeps_list,Deps_list,counter])

    # Create the intial neighbors and start DFS-Algo
    Dim5_LIFO(stack[1],stack,LO_dict,result_list,all_diams,Num_all_subs,Num_leftovers)

    return unique!(result_list)
end



################################################################################
################################################################################
# Encoded section
################################################################################
################################################################################


@doc raw"""
    En_Diamond_prop(en_indeps::AbstractVector{AbstractVector{Int}},
                    en_deps::AbstractVector{AbstractVector{Int}},
                    en_all_diams=AbstractVector{AbstractVector{AbstractVector{Int}}})

    Returns if the union list of `en_indeps` and `en_deps` satisfies the q-matroid diamond condtion.
    Note: This is required to speed up the computations in the below enumeration functions.
"""
# Changes to old version:
# There is no old version

function En_Diamond_prop(en_indeps::AbstractVector{AbstractVector{Int}},
                         en_deps::AbstractVector{AbstractVector{Int}},
                         en_all_diams::AbstractVector{AbstractVector{AbstractVector{Int}}})
    holds = true

    # Put all current spaces together in one list
    en_all_current_spaces = union(en_indeps,en_deps)
    
    # Sort them w.r.t to their subspace dimension
    sort!(en_all_current_spaces, by = x -> length(x))

    # Here we put in all possible encoded diamonds of the encoded vector_space, not only those in the encoded current spaces
    # Check which of all the encoded diamonds of the encoded v.s. is in encoded the current_spaces_list
    en_diams = []
    for elm in en_all_diams
        if issubset(elm,en_all_current_spaces)
            push!(en_diams,elm)
        end
    end

    # Check if all currently possible encoded diamonds satisfy the one of the four possible options
    for diam in en_diams
        sort!(diam, by = x -> length(x))
        overall_count = 0
        if diam[1] in en_indeps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_deps
                        overall_count += 1
                        break
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in en_deps
                        overall_count += 1
                        break
                    end
                elseif elm == diam[length(diam)]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
            end
            # mixed diamond
            count = 0
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in en_indeps
                        continue
                    elseif elm in en_deps
                        count += 1
                    end
                elseif elm == diam[length(diam)]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
                if count > 1
                    overall_count += 1
                    break
                end
            end

        elseif diam[1] in en_deps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_indeps
                        overall_count += 1
                        break
                    end
                end
            end
            # mixed diamond
            for elm in diam
                if elm != diam[1]
                    if elm in en_indeps
                        overall_count +=1
                        break
                    end
                end
            end
        end

        if overall_count >= 4
            holds = false
            break
        end
    end

    return holds
end


################################################################################
# Enumeration of rank-2 q-matroids
################################################################################


@doc raw"""
    
"""
# Changes to old version:
# There is no old version

function En_create_neighbors(node::AbstractVector,
    lo_dict::AbstractDict,
    en_all_diams::AbstractVector{AbstractVector{AbstractVector{Int}}},
    en_all_spaces::AbstractVector{AbstractVector{Int}},
    char::Oscar.IntegerUnion,
    dim::Oscar.IntegerUnion)

    # Increase the depth of the tree
    New_counter = node[3] + 1

    # Get the encoded space which are not assigned yet
    con_sp = collect(values(lo_dict))[New_counter][2]
    compl_list = [elm for elm in con_sp if (!(elm in node[1]) && !(elm in node[2]))]

    # Helperlist
    two_sp_cont = [x for x in con_sp if length(x)==q_binomcoeff(char,2,1)+1]
    two_sp_not_compl = [x for x in two_sp_cont if !(x in compl_list)]
    
    # Decide the possible options
    En_Options = []
    for i in range(1,dim)
    # 1. options: 0-dim loop space
        if i == 1
            if two_sp_cont != []
                right_count = 0
                for elm in two_sp_cont
                    if elm in node[1]
                        right_count += 1
                    elseif elm in compl_list
                        right_count += 1
                    end
                end
                
                if right_count == q_binomcoeff(char,dim-1,1)
                    New_Indeps_list = copy(node[1]) 
                    New_Deps_list = copy(node[2])
                    for elm in compl_list
                        push!(New_Indeps_list,elm)
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                        push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                    end
                end
            end
    # 2. options: 1-dim loop space
        elseif i == 2
            if two_sp_not_compl != []
                if !(two_sp_not_compl[1] in node[2])
                    for elmx in compl_list
                        New_Indeps_list = copy(node[1]) 
                        New_Deps_list = copy(node[2])
                        push!(New_Deps_list,elmx)
                        for elmy in compl_list
                            if elmy != elmx
                                push!(New_Indeps_list,elmy)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                            push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                        end
                    end
                end
            else
                for elmx in compl_list
                    New_Indeps_list = copy(node[1]) 
                    New_Deps_list = copy(node[2])
                    push!(New_Deps_list,elmx)
                    for elmy in compl_list
                        if elmy != elmx
                            push!(New_Indeps_list,elmy)
                        end
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                        push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                    end
                end
            end
    # 3. options: 1-dim loop space (already assigned element)
        elseif i == 3
            inters = intersect(two_sp_not_compl,node[2])
            if inters != []
                for elmx in inters
                    New_Indeps_list = copy(node[1]) 
                    New_Deps_list = copy(node[2])
                    for elmy in compl_list
                        push!(New_Indeps_list,elmy)
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                        push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                    end
                end
            end
    # 4. options: 2-dim loop space
        elseif i == 4
            con_diams = [x for x in en_all_diams if issubset(x,con_sp) && length(x[1])==2]
            if con_diams != []
                for diam in con_diams
                    twos = [x for x in diam if length(x)==q_binomcoeff(char,2,1)+1]
                    if issubset(twos,compl_list)
                        New_Indeps_list = copy(node[1]) 
                        New_Deps_list = copy(node[2])
                        for elm in twos
                            push!(New_Deps_list,elm)
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                            push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                        end
                    elseif intersect(twos,node[2]) != []
                        New_Indeps_list = copy(node[1]) 
                        New_Deps_list = copy(node[2])
                        for elm in twos
                            if !(elm in node[2])
                                push!(New_Deps_list,elm)
                            end
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                            push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                        end
                    end
                end
            end
    # 5. options: 3-dim loop space
        elseif i == 5
            new_con_sp = sort(AbstractVector{AbstractVector{Int}}([x for x in con_sp if length(x)<=q_binomcoeff(char,4,1)+1]),by = x->length(x))
            con_3_int = encoded_k_interval(new_con_sp,char,3,en_all_spaces)
            if con_3_int != []
                for int in con_3_int
                    sort!(int,by = x->length(x))
                    twos = [x for x in int if length(x)==q_binomcoeff(char,2,1)+1]
                    if issubset(twos,compl_list)
                        New_Indeps_list = copy(node[1]) 
                        New_Deps_list = copy(node[2])
                        for elm in twos
                            push!(New_Deps_list,elm)
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                            push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                        end
                    elseif intersect(twos,node[2]) != []
                        New_Indeps_list = copy(node[1]) 
                        New_Deps_list = copy(node[2])
                        for elm in twos
                            if !(elm in node[2])
                                push!(New_Deps_list,elm)
                            end
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,en_all_diams)
                            push!(En_Options,[New_Indeps_list,New_Deps_list,New_counter])
                        end
                    end
                end
            end
        end
    end

    return En_Options

end

function En_LIFO(current_node::AbstractVector,
    stack::AbstractVector,
    lo_dict::AbstractDict,
    result_list::AbstractVector,
    en_all_diams::AbstractVector{AbstractVector{AbstractVector{Int}}},
    en_all_spaces::AbstractVector{AbstractVector{Int}},
    num_all_subs::Oscar.IntegerUnion,
    num_leftovers::Oscar.IntegerUnion,
    char:: Oscar.IntegerUnion,
    dim:: Oscar.IntegerUnion)

    # Calculate the neighbors of the current node
    neighbors = En_create_neighbors(current_node,lo_dict,en_all_diams,en_all_spaces,char,dim)

    # Insert all neigbours of the current node before the node in the stack list
    if length(neighbors) != 0
        for neighbor in neighbors
            insert!(stack,1,neighbor)
        end
    end

    # Remove the current node from the stack
    deleteat!(stack,findall(x-> x == current_node,stack))

    # Gone recursivly through the stack
    for node in stack
        #println(node)
        if node[3] < num_leftovers && length(node[1]) + length(node[2]) < num_all_subs
            En_LIFO(node,stack,lo_dict,result_list,en_all_diams,en_all_spaces,num_all_subs,num_leftovers,char,dim)

        elseif node[3] == num_leftovers || length(node[1]) + length(node[2]) == num_all_subs
            #println("i'm here")
            maxis = [node[1][x] for x in findall(y->length(y)==maximum(length,node[1]),node[1])]
            push!(result_list,[node[1],node[2],maxis])
        end
    end

end

function En_q_matroid_DFS(QM::Q_Matroid)
    # Define all necesssary variables
    Indeps_list = AbstractVector{AbstractVector{Int}}([])
    Deps_list = AbstractVector{AbstractVector{Int}}([])
    Stack = []
    Result_list = []
    Counter = 0

    # Get the Indeps, Deps and Dimension of the Input
    Init_Dim = ncols(QM.groundspace)
    Init_Field = base_ring(QM.groundspace)
    Init_char = Int(characteristic(Init_Field))
    Init_Indeps = Q_Matroid_Independentspaces(QM)
    Init_Deps = Q_Matroid_Dependentspaces(QM)

    # Transform the intial Input
    Trans_Indeps = standard_embedding_higher_dim(Init_Indeps,Init_Dim+1)
    if Init_Deps != []
        Trans_Deps = standard_embedding_higher_dim(Init_Deps,Init_Dim+1)
    else
        Trans_Deps = AbstractVector{fpMatrix}([])
    end

    # Compute all spaces of the ambient space
    All_sp = sort(all_subspaces(Init_Field,Init_Dim+1), by = x -> rank(x))
    Num_all_sp = length(All_sp)
    Ones_dict = OrderedDict([id-1=>elm for (id,elm) in enumerate(All_sp) if rank(elm)==1])

    # Encode the tranformed spaces 
    En_all_sp = sub_encoding(All_sp,Ones_dict)
    En_one_sp = [elm for elm in En_all_sp if length(elm)==2]
    En_Trans_Indeps = sub_encoding(Trans_Indeps,Ones_dict)
    if Trans_Deps != []
        En_Trans_Deps = sub_encoding(Trans_Deps,Ones_dict)
    else
        En_Trans_Deps = AbstractVector{AbstractVector{Int}}([])
    end

    # Create all encoded diamonds of the encoded ambient space
    En_all_diams = encoded_k_interval(En_all_sp,Init_char,2,En_all_sp)

    # Fill Indeps and Deps Lists with the encoded tranformed Init-Input
    for elm in En_Trans_Indeps
        push!(Indeps_list,elm)
    end
    for elm in En_Trans_Deps
        push!(Deps_list,elm)
    end

    # Create the `LO_dict` and declare them all to be independent
    LO_dict = OrderedDict([])
    index = 1
    for elm in En_one_sp
        if (!(elm in Indeps_list) && !(elm in Deps_list))
            merge!(LO_dict,Dict(index=>[elm,encoded_containments_fix_space(elm,En_all_sp)]))
            index += 1
        end
    end
    #LO_dict = OrderedDict([id => [elm,encoded_containments_fix_space(elm,En_all_sp)] for (id,elm) in enumerate(En_one_sp) if (!(elm in Indeps_list) && !(elm in Deps_list))])
    union!(Indeps_list,[x[1] for x in collect(values(LO_dict))])
    Num_leftovers = length(LO_dict)

    # Declare all encoded spaces which have dim. greate equal 2 as dependent
    En_dim_two = q_binomcoeff(Init_char,2,1)+1 
    Bad_en_dims = [1,2,En_dim_two]
    for elm in En_all_sp
        if !(length(elm) in Bad_en_dims) && !(elm in Deps_list) && !(elm in Indeps_list)
            push!(Deps_list,elm)
        end
    end

    # Looking for loops, so all encoded dim.-2 spaces can be declared dependent
    for elm in Deps_list
        if length(elm) == 2
            super_sp = [x for x in encoded_containments_fix_space(elm,En_all_sp) if (length(x)==En_dim_two && !(x in Deps_list) && !(x in Indeps_list))]
            union!(Deps_list,super_sp)
        end
    end

    # Now push the Tuple [Indeps_list,Deps_list,Counter] into the stack
    push!(Stack,[Indeps_list,Deps_list,Counter])

    # Start the DFS-Algo
    En_LIFO(Stack[1],Stack,LO_dict,Result_list,En_all_diams,En_all_sp,Num_all_sp,Num_leftovers,Init_char,Init_Dim+1)

    return unique!(Result_list)

end