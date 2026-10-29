################################################################################
##  Properties and basic functions
################################################################################
using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices
include("q_matroids.jl")

###########################################################################################
# !!!Any matrix you input in a function/method needs to be in RREF!!!
###########################################################################################

@doc raw"""
    Q_Matroid_Independentspaces(QM::Q_Matroid)

    Returns the independent spaces of the q-matroid.
"""

function Q_Matroid_Independentspaces(QM::Q_Matroid)
    Bases = QM.bases

    q_mat_indep_spaces = AbstractVector{Any}([])
    for basis in Bases
        basis_subspaces = subspaces_fix_space(basis)
        for arr in basis_subspaces
            for elm in arr
                push!(q_mat_indep_spaces,elm)
            end
        end
    end

    q_mat_indep_spaces = sort(unique!(q_mat_indep_spaces), by =  x -> rank(x))
    
    return q_mat_indep_spaces
    
end
################################################################################

@doc raw"""
    Q_Matroid_Dependentspaces(QM::Q_Matroid, sub_lat=nothing::Union{Nothing,Any})

    Returns the dependent spaces of the q-matroid.
"""

function Q_Matroid_Dependentspaces(QM::Q_Matroid,sub_lat=nothing::Union{Nothing,Any})
    Field = base_ring(QM.bases[1])
    dim = ncols(QM.groundspace)
    q_mat_dep_spaces = AbstractVector{Any}([])
    
    if isnothing(sub_lat)
        all_subs = all_subspaces(Field,dim)
    else
        all_subs = sub_lat
    end

    # Compute independent-space
    Indeps = Q_Matroid_Independentspaces(QM)

    # Decide wether a space is in Indeps or not
    for elm in all_subs
        if !(elm in Indeps)
            push!(q_mat_dep_spaces,elm)
        end
    end

    return q_mat_dep_spaces
    
end
################################################################################

@doc raw"""
    Q_Matroid_Loopspace(QM::Q_Matroid)

    Returns the loop space of the q-matroid.
"""

function Q_Matroid_Loopspace(QM::Q_Matroid)
    Deps = Q_Matroid_Dependentspaces(QM)

    if Deps != []
        min_dim = minimum(y->rank(y),Deps)
        if min_dim == 1 
            return AbstractVector{Any}([x for x in Deps[findall(y->rank(y)==min_dim,Deps)]])
        else
            return []
        end
    else
        return []
    end
    
end
################################################################################

@doc raw"""
    Q_Matroid_Ranks(QM::Q_Matroid, Space::Any, indeps=nothing::Union{Nothing,Any}, deps=nothing::Union{Nothing,Any})

    Returns the rank of a specific space for the given q-matroid.

    Additionally, inputting the independent and dependent spaces of the q-matroid makes it computationally faster.
"""

function Q_Matroid_Ranks(QM::Q_Matroid, Space::Any, indeps=nothing::Union{Nothing,Any}, deps=nothing::Union{Nothing,Any})

    # Check if the optional arguments are used
    if isnothing(indeps) && isnothing(deps)
        Indeps = Q_Matroid_Independentspaces(QM)
        Deps = Q_Matroid_Dependentspaces(QM)
    else
        Indeps = indeps
        Deps = deps
    end

    # Convert a space not in rref in rref space
    New_space = rref(Space)[2]

    New_space_set = subspace_set(New_space)
    indep_spaces_in_New_Space = []

    if New_space in Indeps
        return rank(New_space)

    elseif New_space in Deps
        for indep_space in Indeps
            if issubset(subspace_set(indep_space),New_space_set)
                push!(indep_spaces_in_New_Space,indep_space)
            end
        end

        if rank(New_space) == 1
            return 0
        else
            if length(indep_spaces_in_New_Space) == 1
                return 0
            else
                return maximum(y->rank(y),indep_spaces_in_New_Space)
            end
        end
    end
end
################################################################################

@doc raw"""
    Q_Matroid_Circuits(QM::Q_Matroid)

    Returns the circuits of the q-matroid.
"""

function Q_Matroid_Circuits(QM::Q_Matroid)
    Indeps = Q_Matroid_Independentspaces(QM)
    Deps = Q_Matroid_Dependentspaces(QM)
    q_mat_circuits = AbstractVector{Any}([])
    not_correct_spaces = []

    for dep_space in Deps
        loop_breaker = true
        arrays_subs = subspaces_fix_space(dep_space)
        deleteat!(arrays_subs, rank(dep_space)+1)
        for array in arrays_subs
            if loop_breaker == false
                break
            else
                for space in array
                    if space in Indeps
                        continue
                    else
                        loop_breaker = false
                        push!(not_correct_spaces,dep_space)
                        break
                    end
                end
            end
        end
    end

    for dep_space in Deps
        if !(dep_space in not_correct_spaces)
            push!(q_mat_circuits,dep_space)
        end
    end

    return unique(q_mat_circuits)

end


@doc raw"""
    Q_Matroid_CircuitsV2(QM::Q_Matroid)

    Returns the circuits of the q-matroid.
"""
# Faster version.

function Q_Matroid_CircuitsV2(QM::Q_Matroid)
    Indeps = Q_Matroid_Independentspaces(QM)
    Deps = Q_Matroid_Dependentspaces(QM)
    q_mat_circuits = AbstractVector{Any}([])

    for dep_space in Deps
        hps = codim_one_subs(dep_space)
        if issubset(hps,Indeps)
            push!(q_mat_circuits,dep_space)
        else
            continue
        end 
    end

    return unique(q_mat_circuits)

end

################################################################################

@doc raw"""
    Is_paving_q_matroid(QM::Q_Matroid)

    Returns `true` if the given q-matroid is paving, i.e., all its circuits have dimension >= rank(QM).
"""

function Is_paving_q_matroid(QM::Q_Matroid)
    q_rank = rank(QM.bases[1])

    right_ones = []
    Circuits = Q_Matroid_CircuitsV2(QM)

    for circ in Circuits
        if  rank(circ) >= q_rank
            push!(right_ones,circ)
        end
    end

    if right_ones == Circuits
        return true
    else
        return false
    end
    
end
################################################################################

@doc raw"""
    Is_sparsepaving_q_matroid(QM::Q_Matroid)

    Returns if the given the q-matroid is sparse paving, i.e., the q-matroid and its dual are both paving.
"""

function Is_sparsepaving_q_matroid(QM::Q_Matroid)
    DQM = Dual_Q_Matroid(QM)
    if Is_paving_q_matroid(QM) && Is_paving_q_matroid(DQM)
        return true
    else
        return false
    end
end
################################################################################

@doc raw"""
    Q_Matroid_Closure_Function(QM::Q_Matroid, space::Any)

    Returns the closure of `space` in terms of the ranks coming from the given q-Matroid.
"""

function Q_Matroid_Closure_Function(QM::Q_Matroid, space::Any)
    Field = base_ring(QM.groundspace)
    dim = ncols(QM.bases[1])
    # zero_mat = matrix_space(Field,1,dim)(1)
    # zero_vec = zero_mat[1,:]

    # Compute Indeps and Deps for rank function
    Indeps = Q_Matroid_Independentspaces(QM)
    Deps = Q_Matroid_Dependentspaces(QM)

    # Compute current rank of given space
    space_rank = Q_Matroid_Ranks(QM,space,Indeps,Deps)

    # Compute list of all one-spaces
    all_ones = subspaces_fix_dim(Field,1,dim)
    all_ones_of_space = dim_one_subs(space)

    right_ones = AbstractVector{Any}([])
    for elm in all_ones
        if !(elm in all_ones_of_space)
            sum = sum_vsV2(space,elm)
            if Q_Matroid_Ranks(QM,sum,Indeps,Deps) == space_rank
                push!(right_ones,elm)
            else
                continue
            end
        end
    end
    
    # Push the space itself in the right_ones list
    push!(right_ones,space)

    # Sum the 
    New_mat = reduce(vcat,right_ones)
    r,rref_mat = rref(New_mat)

    if r == 0
        return rref_mat[1,:]
    else
        return rref_mat[1:r,:]
    end

end
################################################################################


@doc raw"""
    Q_Matroid_CyclicClosure_Function(QM::Q_Matroid, space::Any)

    Returns the cyclic closure of `space` in  terms of the circuits coming from the given q-Matroid.
"""

function  Q_Matroid_CyclicClosure_Function(QM::Q_Matroid, space::Any)
    Circs = Q_Matroid_CircuitsV2(QM)
    field = base_ring(QM.groundspace)
    dim = ncols(QM.groundspace)

    space_subs_lists = subspaces_fix_space(space)
    space_subs = AbstractVector{Any}([])
    for list in space_subs_lists
        for elm in list
            push!(space_subs,elm)
        end
    end

    # Get all the circuits contained in the given `space`
    space_circs = intersect(Circs,space_subs)

    # Add all these circuits together if there is Anything to add
    if space_circs == []
        zero_vec = matrix_space(field,1,dim)(0)
        return zero_vec
    else
        cyc_cl = multisum_vs(space_circs)
        return cyc_cl
    end
   
end
################################################################################


@doc raw"""
    Is_full_q_matroid(QM::Q_Matroid)

    Returns `true` if the given q-Matroid is full, i.e., cyc(E)=E and cl(0)=0.
"""

function Is_full_q_matroid(QM::Q_Matroid)
    dim = ncols(QM.groundspace)
    field = base_ring(QM.groundspace)
    zero_vec = matrix(field,zeros(Int,1,dim))

    cl_zero = Q_Matroid_Closure_Function(QM,zero_vec)
    cyc_ground = Q_Matroid_CyclicClosure_Function(QM,QM.groundspace)

    if cyc_ground == QM.groundspace
        if cl_zero == zero_vec
            return true
        else
            return false
        end
    else
        return false
    end

end
################################################################################


@doc raw"""
    Q_Matroid_Flats(QM::Q_Matroid)

    Returns the flats of the given q-matroid.
"""

function Q_Matroid_Flats(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    n = ncols(Bases[1])

    indeps = Q_Matroid_Independentspaces(QM)
    deps =  Q_Matroid_Dependentspaces(QM)
    one_spaces = subspaces_fix_dim(Field,1,n)
    all_spaces = all_subspaces(Field,n)

    not_correct_spaces = []
    q_matroid_flats = AbstractVector{Any}([])

    for space in all_spaces
        if !(space in Bases)
            one_subs = dim_one_subs(space)
            for one_space in one_spaces
                if !(one_space in one_subs)
                    sum = sum_vsV2(space,one_space)
                    if  Q_Matroid_Ranks(QM,sum,indeps,deps) > Q_Matroid_Ranks(QM,space,indeps,deps)
                        continue
                    else
                        push!(not_correct_spaces,space)
                        break
                    end
                end
            end
        else
            push!(not_correct_spaces,space)
        end
    end

    for space in all_spaces
        if !(space in not_correct_spaces)
            push!(q_matroid_flats,space)
        end
    end

    return q_matroid_flats
end
################################################################################


@doc raw"""
    Q_Matroid_Hyperplanes(QM::Q_Matroid)

    Returns the hyperplanes, i.e., maximal proper flats.
"""

function Q_Matroid_Hyperplanes(QM::Q_Matroid)
    id_mat = QM.groundspace

    flats = Q_Matroid_Flats(QM)
    cleaned_flats = [space for space in flats if space != id_mat]
    q_hyperplanes = AbstractVector{Any}([])

    for elm in cleaned_flats
        cont_list = [x for x in containments_fix_space(elm) if x != elm]
        inters = intersect(cont_list,cleaned_flats)
        if inters == []
            push!(q_hyperplanes,elm)
        else
            continue
        end
    end
    
    return q_hyperplanes

end
################################################################################


@doc raw"""
    Q_Matroid_CircuitHyperplanes(QM::Q_Matroid)

    Returns the circuit-hyperplanes, i.e., the subspaces that are simultaniously circuits and hyperplanes.
"""
function Q_Matroid_CircuitHyperplanes(QM::Q_Matroid)
    circs = Q_Matroid_CircuitsV2(QM)
    hyps = Q_Matroid_Hyperplanes(QM)

    return intersect(circs,hyps)
    
end
################################################################################

@doc raw"""
    Q_Matroid_CyclicFlats(QM::Q_Matroid)

    Returns the cyclic flats, i.e., flats that are also open spaces.
"""

function Q_Matroid_CyclicFlats(QM::Q_Matroid)
    flats = Q_Matroid_Flats(QM)
    openspaces = Q_Matroid_Openspaces(QM)

    q_cyclic_flats = intersect(flats,openspaces)

    return q_cyclic_flats

end
################################################################################

@doc raw"""
    Is_Schubert_q_matroid(QM::Q_Matroid)

    Returns a boolean indicating whether the q-matroid is a Schubert q-matroid, i.e., its cyclic flats form a chain under inclusion.
"""

function Is_Schubert_q_matroid(QM::Q_Matroid)
    cyclic_flats = Q_Matroid_CyclicFlats(QM)
    sets_cyclic_flats = [subspace_set(x) for x in cyclic_flats]
    holds = true

    # Check if the cyclic flats form a chain under inclusion
    for pair in Oscar.combinations(sets_cyclic_flats,2)
        if issubset(pair[1],pair[2]) || issubset(pair[2],pair[1])
            continue
        else
            holds = false
            break
        end
    end
    
    return holds
end


@doc raw"""
    Q_Matroid_Spanningspaces(QM::Q_Matroid)

    Returns the spanning spaces, i.e., all subspaces which have full rank.
"""

function Q_Matroid_Spanningspaces(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    q_rank = rank(Bases[1]) 
    dim =  ncols(Bases[1])
    indeps = Q_Matroid_Independentspaces(QM)
    deps = Q_Matroid_Dependentspaces(QM)
    all_subs = all_subspaces(Field,dim)

    # Push all spaces with have rank equal to `q_rank`
    spanning_spaces = AbstractVector{Any}([])
    for sub in all_subs
        if Q_Matroid_Ranks(QM,sub,indeps,deps) == q_rank
            push!(spanning_spaces,sub)
        else
            continue
        end
    end

    return spanning_spaces
    
end
################################################################################


@doc raw"""
    Q_Matroid_Non_Spanningspaces(QM::Q_Matroid)

    Returns the non-spanning spaces of the given q-matroid.
"""

function Q_Matroid_Non_Spanningspaces(QM::Q_Matroid)
    Field = base_ring(QM.groundspace)
    dim = ncols(QM.bases[1])
    all_subs = all_subspaces(Field,dim)
    span_spaces = Q_Matroid_Spanningspaces(QM)
    Non_spanning_spaces = AbstractVector{Any}([])

    for space in all_subs
        if !(space in span_spaces)
            push!(Non_spanning_spaces,space)
        else
            continue
        end
    end

    return Non_spanning_spaces

end
################################################################################


@doc raw"""
    Q_Matroid_Openspaces(QM::Q_Matroid)

    Returns the open spaces, i.e., subspaces which are sums of circtuits.
"""

function Q_Matroid_Openspaces(QM::Q_Matroid)
    dual = Dual_Q_Matroid(QM)
    flats = Q_Matroid_Flats(dual)

    Openspaces = AbstractVector{Any}([])

    for space in flats
        dual_flat = orthogonal_complementV2(space)[1]
        push!(Openspaces,dual_flat)
    end

    return Openspaces

end
################################################################################


@doc raw"""
    Q_Matroid_lattice(QM::Q_Matroid, Indeps::Any, Deps::Any, show::String)

    Returns the lattice of the q-matroid as a graph, where we only draw edges that increase the rank.

    This function requires the independent and dependent spaces of the q-matroid, because it's computationally faster.

    For the `show` attribute, you have to set "yes" or "no", telling the function whether to plot the graph.  
"""

function Q_Matroid_lattice(QM::Q_Matroid, Indeps::Any, Deps::Any, show::String)
    Bases = QM.bases
    Field = base_ring(Bases[1])
    char = Int(characteristic(Field))
    num_nodes = 0
    node_pos_x = Array{Int64}([])
    node_pos_y = Array{Int64}([])

    nodelabel = []
    nodelabel_as_array=OrderedDict([])
    dim = ncols(Bases[1])

    # Create the nodes
    for i in range(0,dim)
        num_nodes += q_binomcoeff(char,dim,i)
    end

    for i in range(0, dim)
        for j in range(1,q_binomcoeff(char,dim,i))
            push!(node_pos_y,Int(i))
        end
        for j in range(1,q_binomcoeff(char,dim,i))
            push!(node_pos_x,Int(j))
        end
    end

    # Create the labels
    all_subs = sort(all_subspaces(Field,dim),by = z->rank(z))
    
    for (id,elm) in enumerate(all_subs)
        push!(nodelabel,elm)
        merge!(nodelabel_as_array,OrderedDict(id=>[elm,subspace_set(elm),Q_Matroid_Ranks(QM,elm,Indeps,Deps)]))
    end

    G = SimpleGraph(num_nodes)

    helper_list = []
    for (key,value) in nodelabel_as_array
        push!(helper_list,((key,value)))
    end

    #Create the edges
    for pair in Oscar.combinations(helper_list,2)
        if issubset(pair[1][2][2],pair[2][2][2]) || issubset(pair[2][2][2],pair[1][2][2])
            if rank(pair[1][2][1]) + 1 == rank(pair[2][2][1]) || rank(pair[2][2][1]) + 1 == rank(pair[1][2][1])  
                if pair[2][2][3] == pair[1][2][3] + 1 || pair[1][2][3] == pair[2][2][3] + 1
                    Graphs.add_edge!(G,pair[1][1],pair[2][1])
                end
            end
        end
    end

    if show == "yes"
        return GraphPlot.gplot(G,node_pos_x,node_pos_y,NODELABELSIZE=2.0,nodelabelc="red",nodelabel=nodelabel)
    elseif show == "no"
        return G
    else
        return helper_list
    end
    
end


@doc raw"""
    Q_Matroid_latticeV2(QM::Q_Matroid, Indeps::AbstractVector{Any}, Deps::AbstractVector{Any}, show::String)

    Returns the lattice of the q-matroid as a graph, where we only draw edges that increase the rank.

    This function requires the independent and dependent spaces of the q-matroid, because it's computationally faster.

    For the `show` attribute, you have to set "yes" or "no", telling the function whether to plot the graph.  
"""
# This version uses Oscar methods to create the graph. !!!Preferred!!! 

function Q_Matroid_latticeV2(QM::Q_Matroid, Indeps::Any, Deps::Any)
    Bases = QM.bases
    Field = base_ring(Bases[1])
    char = Int(characteristic(Field))
    num_nodes = 0

    nodelabel_as_array=OrderedDict([])
    dim = ncols(Bases[1])

    # Create the nodes
    for i in range(0,dim)
        num_nodes += q_binomcoeff(char,dim,i)
    end

    # Create the labels
    all_subs = sort(all_subspaces(Field,dim),by = z->rank(z))
    
    for (id,elm) in enumerate(all_subs)
        merge!(nodelabel_as_array,OrderedDict(id=>[elm,subspace_set(elm),Q_Matroid_Ranks(QM,elm,Indeps,Deps)]))
    end

    G = Oscar.Graph{Undirected}(num_nodes)

    helper_list = []
    for (key,value) in nodelabel_as_array
        push!(helper_list,((key,value)))
    end

    # Create the edges
    for pair in Oscar.combinations(helper_list,2)
        if issubset(pair[1][2][2],pair[2][2][2]) || issubset(pair[2][2][2],pair[1][2][2])
            if rank(pair[1][2][1]) + 1 == rank(pair[2][2][1]) || rank(pair[2][2][1]) + 1 == rank(pair[1][2][1])  
                if pair[2][2][3] == pair[1][2][3] + 1 || pair[1][2][3] == pair[2][2][3] + 1
                    Oscar.add_edge!(G,pair[1][1],pair[2][1])
                end
            end
        end
    end

    return G
    
end
################################################################################


@doc raw"""
    Are_isom_q_matroids(QM1::Q_Matroid, QM2::Q_Matroid)

    Returns if the two q-matroids are isomorphic.
    
    Here we use the underlying q-matroid lattice and check if the graphs are isomorphic. 
"""

function Are_isom_q_matroids(QM1::Q_Matroid, QM2::Q_Matroid)
    indeps_1 = Q_Matroid_Independentspaces(QM1) 
    deps_1 = Q_Matroid_Dependentspaces(QM1)
    lat_1 = Q_Matroid_lattice(QM1,indeps_1,deps_1,"no")
    indeps_2 = Q_Matroid_Independentspaces(QM2)
    deps_2 = Q_Matroid_Dependentspaces(QM2)
    lat_2 = Q_Matroid_lattice(QM2,indeps_2,deps_2,"no")

    return Graphs.Experimental.has_isomorph(lat_1,lat_2)
end


@doc raw"""
    Are_isom_q_matroidsV2(QM1::Q_Matroid, QM2::Q_Matroid, lats=nothing::Union{Nothing,AbstractVector{SimpleGraph}})

    Returns if the two q-matroids are isomorphic.
    
    Here we use the underlying q-matroid lattice and check if the graphs are isomorphic.
"""
# This version uses the method `Q_Matroid_latticeV2`. !!!Preferred!!!

function Are_isom_q_matroidsV2(QM1::Q_Matroid, QM2::Q_Matroid, lats=nothing::Union{Nothing,AbstractVector{SimpleGraph}})
    
    if isnothing(lats)
        indeps_1 = Q_Matroid_Independentspaces(QM1) 
        deps_1 = Q_Matroid_Dependentspaces(QM1)
        l1 = Q_Matroid_lattice(QM1,indeps_1,deps_1,"no")
        indeps_2 = Q_Matroid_Independentspaces(QM2)
        deps_2 = Q_Matroid_Dependentspaces(QM2)
        l2 = Q_Matroid_lattice(QM2,indeps_2,deps_2,"no")

        # Transform Graph.jl Graphs to Oscar Graphs
        edges1 = collect(Graphs.edges(l1))
        edges2 = collect(Graphs.edges(l2))
        vert1 = Graphs.nv(l1)
        vert2 = Graphs.nv(l2)

        new_l1 = Oscar.Graph{Undirected}(vert1)
        new_l2 = Oscar.Graph{Undirected}(vert2)

        for edge in edges1
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_l1,s,d)
        end
        for edge in edges2
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_l2,s,d)
        end

        return Oscar.is_isomorphic(new_l1,new_l2)

    else
        l1 = lats[1]
        l2 = lats[2]

        # Transform Graph.jl-Graphs to Oscar Graphs
        edges1 = collect(Graphs.edges(l1))
        edges2 = collect(Graphs.edges(l2))
        vert1 = Graphs.nv(l1)
        vert2 = Graphs.nv(l2)

        new_l1 = Oscar.Graph{Undirected}(vert1)
        new_l2 = Oscar.Graph{Undirected}(vert2)

        for edge in edges1
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_l1,s,d)
        end
        for edge in edges2
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_l2,s,d)
        end

        return Oscar.is_isomorphic(new_l1,new_l2)
    end

end
################################################################################


@doc raw"""
    isom_classes_from_mats(List_matrices::Any)

    Returns a list of all the different isom. classes of q-matroids coming from the matrices in the initial input list.
    
    Note that these are only isom. classes of representable q-matroids.

    The list is given in the follwing way: (matrix rep.the class, q-mat associated to matrix, length of it's bases, num of elm in the isom. class) 
"""

function Isom_classes_from_mats(list_matrices::Any)
    unique_index = 1
    matrices_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,matrix) in enumerate(list_matrices)
        QM = q_matroid_from_matrix(matrix)
        indeps = Q_Matroid_Independentspaces(QM)
        deps = Q_Matroid_Dependentspaces(QM)
        graph = Q_Matroid_lattice(QM,indeps,deps,"no")
        merge!(matrices_dict,Dict(id=>[matrix,QM,indeps,deps,graph]))
    end

    # Fill key_value_list
    for (key,tuple) in matrices_dict
        push!(key_value_list,(key,tuple[1]))
    end

    # Start values
    start_mat = matrices_dict[unique_index][1]
    start_qm = matrices_dict[unique_index][2]
    start_indeps = matrices_dict[unique_index][3]
    start_deps = matrices_dict[unique_index][4]
    start_l = matrices_dict[unique_index][5]

    #list_of_bases = []
    list_non_isom_q_mats = []
    list_isom_q_mats = []

    while length(key_value_list) > 0
        for elm in key_value_list
            if elm[2] != start_mat
                if Graphs.Experimental.has_isomorph(start_l,matrices_dict[elm[1]][5])
                    push!(list_isom_q_mats,(elm[1],elm[2]))
                else
                    push!(list_non_isom_q_mats,(elm[1],elm[2]))
                end
            end
        end
        push!(list_diff_q_mat,(start_mat,start_qm,length(start_qm.bases),length(list_isom_q_mats)))

        # Reassignements
        if list_non_isom_q_mats == []
            key_value_list = list_non_isom_q_mats
        else
            key_value_list = list_non_isom_q_mats
            start_mat = matrices_dict[key_value_list[unique_index][1]][1]
            start_qm = matrices_dict[key_value_list[unique_index][1]][2]
            start_indeps = matrices_dict[key_value_list[unique_index][1]][3]
            start_deps = matrices_dict[key_value_list[unique_index][1]][4]
            start_l = matrices_dict[key_value_list[unique_index][1]][5]

            list_non_isom_q_mats = []
            list_isom_q_mats = []
        end
    end

    return list_diff_q_mat
    
end


@doc raw"""
    isom_classes_from_matsV2(List_matrices::Any) 

    Returns a list of all the different isom. classes of q-matroids coming from the matrices in the initial input list.
    
    Note that these are only isom. classes of representable q-matroids.

    The list is given in the follwing way: (matrix rep.the class, q-mat associated to matrix, length of it's bases, num of elm in the isom. class)
"""
# This version uses Oscar methods to create the underlying graphs. !!!Preferred!!!

function Isom_classes_from_matsV2(list_matrices::Any)
    unique_index = 1
    matrices_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,matrix) in enumerate(list_matrices)
        QM = q_matroid_from_matrix(matrix)
        indeps = Q_Matroid_Independentspaces(QM)
        deps = Q_Matroid_Dependentspaces(QM)
        graph = Q_Matroid_lattice(QM,indeps,deps,"no")

        # Transform Graph.jl Graphs to Oscar Graphs
        edges = collect(Graphs.edges(graph))
        vert = Graphs.nv(graph)
        new_graph = Oscar.Graph{Undirected}(vert)
        for edge in edges
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_graph,s,d)
        end

        merge!(matrices_dict,Dict(id=>[matrix,QM,indeps,deps,new_graph]))
    end

    # Fill key_value_list
    for (key,tuple) in matrices_dict
        push!(key_value_list,(key,tuple[1]))
    end

    # Start values
    start_mat = matrices_dict[unique_index][1]
    start_qm = matrices_dict[unique_index][2]
    start_indeps = matrices_dict[unique_index][3]
    start_deps = matrices_dict[unique_index][4]
    start_l = matrices_dict[unique_index][5]

    #list_of_bases = []
    list_non_isom_q_mats = []
    list_isom_q_mats = []

    while length(key_value_list) > 0
        for elm in key_value_list
            if elm[2] != start_mat
                #if Are_isom_q_matroidsV2(start_qm,matrices_dict[elm[1]][2],[start_l,matrices_dict[elm[1]][5]])
                if Oscar.is_isomorphic(start_l,matrices_dict[elm[1]][5])
                    push!(list_isom_q_mats,(elm[1],elm[2]))
                else
                    push!(list_non_isom_q_mats,(elm[1],elm[2]))
                end
            end
        end
        push!(list_diff_q_mat,(start_mat,start_qm,length(start_qm.bases),length(list_isom_q_mats)))

        # Reassignements
        if list_non_isom_q_mats == []
            key_value_list = list_non_isom_q_mats
        else
            key_value_list = list_non_isom_q_mats
            start_mat = matrices_dict[key_value_list[unique_index][1]][1]
            start_qm = matrices_dict[key_value_list[unique_index][1]][2]
            start_indeps = matrices_dict[key_value_list[unique_index][1]][3]
            start_deps = matrices_dict[key_value_list[unique_index][1]][4]
            start_l = matrices_dict[key_value_list[unique_index][1]][5]

            list_non_isom_q_mats = []
            list_isom_q_mats = []
        end
    end

    return list_diff_q_mat
    
end
################################################################################


@doc raw"""
    isom_classes_from_bases(List_bases::Any)

    Returns a list of all the different isom. classes of q-matroids coming from the bases collection in the initial input list.

    The list is given in the follwing way: (q-matroid, length of its bases, num of elm in the isom. class) 
"""

function Isom_classes_from_bases(List_bases::Any)
    unique_index = 1
    Bases_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []
    field = base_ring(List_bases[1][1])
    dim = ncols(List_bases[1][1])
    id_mat = matrix_space(field,dim,dim)(1)   

    # Create dict
    for (id,elm) in enumerate(List_bases)
        QM = Q_Matroid(id_mat,elm)
        indeps = Q_Matroid_Independentspaces(QM)
        deps = Q_Matroid_Dependentspaces(QM)
        graph = Q_Matroid_lattice(QM,indeps,deps,"no")
        merge!(Bases_dict,Dict(id=>[QM,indeps,deps,graph]))
    end

    # Fill key_value_list
    for (key,tuple) in Bases_dict
        push!(key_value_list,(key,tuple[1].bases))
    end

    # Start values
    start_qm = Bases_dict[unique_index][1]
    start_indeps = Bases_dict[unique_index][2]
    start_deps = Bases_dict[unique_index][3]
    start_l = Bases_dict[unique_index][4]

    #list_of_bases = []
    list_non_isom_q_mats = []
    list_isom_q_mats = []

    while length(key_value_list) > 0
        for elm in key_value_list
            if elm[2] != start_qm.bases
                if Graphs.Experimental.has_isomorph(start_l,Bases_dict[elm[1]][4])
                    push!(list_isom_q_mats,(elm[1],elm[2]))
                else
                    push!(list_non_isom_q_mats,(elm[1],elm[2]))
                end
            end
        end
        push!(list_diff_q_mat,(start_qm,length(start_qm.bases),length(list_isom_q_mats)))

        # Reassignements
        if list_non_isom_q_mats == []
            key_value_list = list_non_isom_q_mats
        else
            key_value_list = list_non_isom_q_mats
            start_qm = Bases_dict[key_value_list[unique_index][1]][1]
            start_indeps = Bases_dict[key_value_list[unique_index][1]][2]
            start_deps = Bases_dict[key_value_list[unique_index][1]][3]
            start_l = Bases_dict[key_value_list[unique_index][1]][4]

            list_non_isom_q_mats = []
            list_isom_q_mats = []
        end
    end

    return list_diff_q_mat
end


@doc raw"""
    isom_classes_from_basesV2(List_bases::Any)

    Returns a list of all the different isom. classes of q-matroids coming from the bases collection in the initial input list.

    The list is given in the follwing way: (q-matroid, length of its bases, num of elm in the isom. class) 
"""
# This version uses Oscar methods to create the underlying graphs. !!!Preferred!!!

function Isom_classes_from_basesV2(List_bases::Any)
    unique_index = 1
    Bases_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []
    field = base_ring(List_bases[1][1])
    dim = ncols(List_bases[1][1])
    id_mat = matrix_space(field,dim,dim)(1)  

    # Create dict
    for (id,elm) in enumerate(List_bases)
        QM = Q_Matroid(id_mat,elm)
        indeps = Q_Matroid_Independentspaces(QM)
        deps = Q_Matroid_Dependentspaces(QM)
        graph = Q_Matroid_lattice(QM,indeps,deps,"no")

        # Transform Graph.jl Graphs to Oscar Graphs
        edges = collect(Graphs.edges(graph))
        vert = Graphs.nv(graph)
        new_graph = Oscar.Graph{Undirected}(vert)
        for edge in edges
            s = Graphs.src(edge)
            d = Graphs.dst(edge)
            Oscar.add_edge!(new_graph,s,d)
        end

        merge!(Bases_dict,Dict(id=>[QM,indeps,deps,new_graph]))
    end

    # Fill key_value_list
    for (key,tuple) in Bases_dict
        push!(key_value_list,(key,tuple[1].bases))
    end

    # Start values
    start_qm = Bases_dict[unique_index][1]
    start_indeps = Bases_dict[unique_index][2]
    start_deps = Bases_dict[unique_index][3]
    start_l = Bases_dict[unique_index][4]

    #list_of_bases = []
    list_non_isom_q_mats = []
    list_isom_q_mats = []

    while length(key_value_list) > 0
        for elm in key_value_list
            if elm[2] != start_qm.bases
                if Oscar.is_isomorphic(start_l,Bases_dict[elm[1]][4])
                    push!(list_isom_q_mats,(elm[1],elm[2]))
                else
                    push!(list_non_isom_q_mats,(elm[1],elm[2]))
                end
            end
        end
        push!(list_diff_q_mat,(start_qm,length(start_qm.bases),length(list_isom_q_mats)))

        # Reassignements
        if list_non_isom_q_mats == []
            key_value_list = list_non_isom_q_mats
        else
            key_value_list = list_non_isom_q_mats
            start_qm = Bases_dict[key_value_list[unique_index][1]][1]
            start_indeps = Bases_dict[key_value_list[unique_index][1]][2]
            start_deps = Bases_dict[key_value_list[unique_index][1]][3]
            start_l = Bases_dict[key_value_list[unique_index][1]][4]

            list_non_isom_q_mats = []
            list_isom_q_mats = []
        end
    end

    return list_diff_q_mat
end
################################################################################


@doc raw"""
    Q_Matroid_charpoly(QM::Q_Matroid, Indeps::Any, Deps::Any)

    Returns the characteristic polynomial of the q-matroid.

    This function requires the independent and dependent spaces of the q-matroid, because it's computationally faster.
"""

function Q_Matroid_charpoly(QM::Q_Matroid, Indeps::Any, Deps::Any)
    Bases = QM.bases
    Field = base_ring(Bases[1])
    dim = ncols(Bases[1])

    # Create polynomial ring over Z
    R,z = polynomial_ring(ZZ,"z")

    # create all subspaces
    all_spaces = sort(all_subspaces(Field,dim), by = x->rank(x))

    # Compute rank of q-matroid
    #max_space = all_spaces[findall(x-> nrows(x)==dim,all_spaces)][1]
    q_mat_rank = rank(Bases[1])

    # Search for zero_vec
    zero_vec = all_spaces[1]

    # Create the char-polyn for the given q-matroid
    char_polyn = R(0)
    
    for space in all_spaces
        diff = q_mat_rank-Q_Matroid_Ranks(QM,space,Indeps,Deps)
        char_polyn += Möbius_func_subspace_lat(zero_vec,space)*z^(diff)
    end
     
    return char_polyn
end
################################################################################


@doc raw"""
    Projectivization_matroid(QM::Q_Matroid, Indeps::AbstractVector{Any}, Deps::AbstractVector{Any})

    Returns the projectivization matroid of the given q-matroid.
"""

function Projectivization_matroid(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    dim = ncols(Bases[1])
    q_rank = rank(Bases[1])
    one_spaces = subspaces_fix_dim(Field,1,dim)
    groundset_dictionary = OrderedDict([])
    groundset = []

    # Assign each 1-space a number
    for (id,elm) in enumerate(one_spaces)
        merge!(groundset_dictionary,Dict(Int(id)=>elm))
        push!(groundset,Int(id))
    end

    # Creating the bases of the projectivization matroid
    proj_mat_bases_helper_list = []
    for basis in Bases
        one_subs = dim_one_subs(basis)
        id_sub_pair_list = []
        for (id,value) in groundset_dictionary
            for space in one_subs
                if space == value
                    push!(id_sub_pair_list,(id,value))
                end
            end
        end

        for combi in Oscar.combinations(id_sub_pair_list,q_rank)
            new_combi = [x[2] for x in combi]
            mat = vcat(new_combi)
            if rank(mat) == q_rank
                push!(proj_mat_bases_helper_list,combi)
            else
                continue
            end
        end
    end
    proj_mat_bases_helper_list = unique(proj_mat_bases_helper_list)

    # Translate everything
    proj_mat_bases = AbstractVector{AbstractVector{Any}}([])
    for combi in proj_mat_bases_helper_list
        sub_list = []
        for pair in combi
            push!(sub_list,pair[1])
        end
        push!(proj_mat_bases,sub_list)
    end


    # Instantiate the matroid
    proj_mat = matroid_from_bases(proj_mat_bases,length(groundset))

    return proj_mat
    
end
################################################################################


@doc raw"""
    Dual_Q_Matroid(QM::Q_Matroid)

    Returns the dual q-matroid for the given q-matroid, w.r.t. the standard dot product. 
"""

function Dual_Q_Matroid(QM::Q_Matroid)
    Bases = QM.bases
    bases_dual_q_matroid = AbstractVector{Any}([])

    for basis in Bases
        dual_basis = orthogonal_complementV2(basis)[1]
        push!(bases_dual_q_matroid,dual_basis)
    end

    Dual_QM = Q_Matroid(QM.groundspace,bases_dual_q_matroid)

    return Dual_QM
end
################################################################################

@doc raw"""
    Q_Matroid_Aut(QM::Q_Matroid)

    Returns the automorphism group of the given q-Matroid.
"""

function Q_Matroid_Aut(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    Dim = ncols(QM.groundspace)
    Gln = Oscar.general_linear_group(Dim, Field)
    Gln_elements = collect(Oscar.elements(Gln))

    # Check for every matrix in `gln` if the multiplication with every bases-element is still a bases-element
    gen_mats = AbstractVector{MatrixGroupElem}([])
    for mat in Gln_elements
        hold = true
        for base in Bases
            prod = rref(transpose(mat*transpose(base)))[2]
            if !(prod in Bases)
                hold = false
                break
            end
        end
        if hold
            push!(gen_mats,mat)
        end
    end
 
    return matrix_group(gen_mats)
end
################################################################################