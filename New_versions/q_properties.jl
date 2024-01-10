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
include("./q_matroids.jl")

@doc raw"""
    Q_Matroid_Indepentspaces(QM::Q_Matroid)

    This returns the Indepentspaces of the Q-Matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) using `base_ring`-func. instead of old struct `field`-attribute
# (3) got rid of in-func. varible `Field`

function Q_Matroid_Indepentspaces(QM::Q_Matroid)
    Bases = QM.bases

    q_mat_indep_spaces = AbstractVector{fpMatrix}([])
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
    Q_Matroid_Depentspaces(QM::Q_Matroid, sub_lat=nothing::Union{Nothing,AbstractVector{fpMatrix}})

    This returns the Depentspaces of the Q-Matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) using `base_ring`-func. instead of old struct `field`-attribute
# (3) renamed the `choice-variable to `sub_lat`

function Q_Matroid_Depentspaces(QM::Q_Matroid,sub_lat=nothing::Union{Nothing,AbstractVector{fpMatrix}})
    Field = base_ring(QM.bases[1])
    dim = ncols(QM.groundspace)
    q_mat_dep_spaces = AbstractVector{fpMatrix}([])
    
    if isnothing(sub_lat)
        all_subs = all_subspaces(Field,dim)
    else
        all_subs = sub_lat
    end

    # Compute independent-space
    Indeps = Q_Matroid_Indepentspaces(QM)

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

    This returns the Loopspace of the q-matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of in-func. varible `Field`

function Q_Matroid_Loopspace(QM::Q_Matroid)
    Deps = Q_Matroid_Depentspaces(QM)

    if Deps != []
        min_dim = minimum(y->rank(y),Deps)
        if min_dim == 1 
            return AbstractVector{fpMatrix}([x for x in Deps[findall(y->rank(y)==min_dim,Deps)]])
        else
            return []
        end
    else
        return []
    end
    
end
################################################################################


@doc raw"""
    Q_Matroid_Ranks(QM::Q_Matroid, Space::fpMatrix, indeps=nothing::Union{Nothing,AbstractVector{fpMatrix}}, deps=nothing::Union{Nothing,AbstractVector{fpMatrix}})

    This returns the rank of a specific space in a given q-matroid.
    
    We require for this function, the Independent-and Dependent-Spaces, because it's computational faster.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of in-func. varible `Field`
# (3) declaring `indeps` and `deps` varibales to optional arguments

function Q_Matroid_Ranks(QM::Q_Matroid, Space::fpMatrix, indeps=nothing::Union{Nothing,AbstractVector{fpMatrix}}, deps=nothing::Union{Nothing,AbstractVector{fpMatrix}})

    # Check if the optional arguments are used
    if isnothing(indeps) && isnothing(deps)
        Indeps = Q_Matroid_Indepentspaces(QM)
        Deps = Q_Matroid_Indepentspaces(QM)
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

    This returns the circuits of the q-matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of in-func. varible `Field`

function Q_Matroid_Circuits(QM::Q_Matroid)
    Indeps = Q_Matroid_Indepentspaces(QM)
    Deps = Q_Matroid_Depentspaces(QM)
    q_mat_circuits = AbstractVector{fpMatrix}([])
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
"""
# Completely new version

function Q_Matroid_CircuitsV2(QM::Q_Matroid)
    Indeps = Q_Matroid_Indepentspaces(QM)
    Deps = Q_Matroid_Depentspaces(QM)
    q_mat_circuits = AbstractVector{fpMatrix}([])

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

    This returns the circuits of the q-matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of in-func. varible `Field`
# (3) using now `Q_Matroid_CircuitsV2`

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
    Q_Matroid_Closure_Function(QM::Q_Matroid, space::fpMatrix)

    Returns the closure w.r.t. of the given `space` in the terms of ranks coming from the given q-Matroid.
"""
function Q_Matroid_Closure_Function(QM::Q_Matroid, space::fpMatrix)
    Field = QM.field
    dim = ncols(QM.bases[1])
    zero_mat = matrix_space(Field,1,dim)(1)
    zero_vec = zero_mat[1,:]

    # Compute Indeps and Deps for rank function
    Indeps = Q_Matroid_Indepentspaces(QM)
    Deps = Q_Matroid_Depentspaces(QM)

    # Compute current rank of given space
    space_rank = Q_Matroid_Ranks(QM,space,Indeps,Deps)

    # Compute list of all one-spaces
    all_ones = subspaces_fix_dim(Field,1,dim)
    all_ones_of_space = dim_one_subs(Field,space)

    right_ones = AbstractVector{fpMatrix}([])
    for elm in all_ones
        if !(elm in all_ones_of_space)
            sum = sum_vs(Field,space,elm)
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
    New_mat = vcat(right_ones)
    r,rref_mat = rref(New_mat)

    if rref_mat == zero_mat
        return zero_vec
    else
        return rref_mat[1:r,:]
    end

end
################################################################################


@doc raw"""
    Q_Matroid_Flats(QM::Q_Matroid)

    This returns the flats of the q-matroid.
"""
# Changes to old version:
    # (1) using now `sum_vsV2`
    # (2) added condition that we not looking at base-spaces anymore

function Q_Matroid_Flats(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    n = ncols(Bases[1])

    indeps = Q_Matroid_Indepentspaces(QM)
    deps =  Q_Matroid_Depentspaces(QM)
    one_spaces = subspaces_fix_dim(Field,1,n)
    all_spaces = all_subspaces(Field,n)

    not_correct_spaces = []
    q_matroid_flats = AbstractVector{fpMatrix}([])

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

    This returns the Hyperplanes, i.e. maximal proper flats, of the q-matroid.
"""
# Changes to old version:
# (1) got rid of in-func. varible `Field`
# (2) using `QM.groundspace` instead of creating a `matrix_space`

function Q_Matroid_Hyperplanes(QM::Q_Matroid)
    id_mat = QM.groundspace

    flats = Q_Matroid_Flats(QM)
    cleaned_flats = [space for space in flats if space != id_mat]
    q_hyperplanes = AbstractVector{fpMatrix}([])

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
    Q_Matroid_CyclicFlats(QM::Q_Matroid)

    This returns the CyclicFlats, i.e. flats that are open spaces as well, of the q-matroid.
"""
# Changes to old version:
# None

function Q_Matroid_CyclicFlats(QM::Q_Matroid)
    flats = Q_Matroid_Flats(QM)
    openspaces = Q_Matroid_Openspaces(QM)

    q_cyclic_flats = intersect(flats,openspaces)

    return q_cyclic_flats

end
################################################################################


@doc raw"""
    Q_Matroid_Spanningspaces(QM::Q_Matroid)

    This returns the Spanning-spaces, i.e. all spaces which have full rank, of the q-matroid.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func

function Q_Matroid_Spanningspaces(QM::Q_Matroid)
    Bases = QM.bases
    Field = base_ring(QM.groundspace)
    q_rank = rank(Bases[1]) 
    dim =  ncols(Bases[1])
    indeps = Q_Matroid_Indepentspaces(QM)
    deps = Q_Matroid_Depentspaces(QM)
    all_subs = all_subspaces(Field,dim)

    # Push all spaces with have rank equal to `q_rank`
    spanning_spaces = AbstractVector{fpMatrix}([])
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

    This returns the Nom-spanning-spaces of the q-matroid.
"""
# Changes to old version:
# None

function Q_Matroid_Non_Spanningspaces(QM::Q_Matroid)
    Field = base_ring(QM.groundspace)
    dim = ncols(QM.bases[1])
    all_subs = all_subspaces(Field,dim)
    span_spaces = Q_Matroid_Spanningspaces(QM)
    Non_spanning_spaces = AbstractVector{fpMatrix}([])

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

    This returns the open-spaces, i.e. subspaces which are sums of circtuits, of the q-matroid.
"""
# Changes to old version:
# (1) got rid of in-func. varible `Field`

function Q_Matroid_Openspaces(QM::Q_Matroid)
    dual = Dual_Q_Matroid(QM)
    flats = Q_Matroid_Flats(dual)

    Openspaces = AbstractVector{fpMatrix}([])

    for space in flats
        dual_flat = orthogonal_complement(space)[1]
        push!(Openspaces,dual_flat)
    end

    return Openspaces

end
################################################################################


@doc raw"""
    Q_Matroid_lattice(QM::Q_Matroid, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix}, show::String)

    This returns the lattice of the q-matroid as graph, where we only draw edges that increase the rank.

    We require for this function, the Independent-and Dependent-Spaces, because it's computational faster.

    For `show`-attribute you have to set "yes" or "no", telling the function to plot the graph or not.  
"""
function Q_Matroid_lattice(QM::Q_Matroid, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix}, show::String)
    Bases = QM.bases
    Field = QM.field
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
    all_subs = sort(all_subspaces(Field,dim),by = z->subspace_dim(Field,z))
    
    for (id,elm) in enumerate(all_subs)
        push!(nodelabel,elm)
        merge!(nodelabel_as_array,OrderedDict(id=>[elm,subspace_set(Field,elm),Q_Matroid_Ranks(QM,elm,Indeps,Deps)]))
    end

    G = SimpleGraph(num_nodes)

    helper_list = []
    for (key,value) in nodelabel_as_array
        push!(helper_list,((key,value)))
    end

    #Create the edges
    for pair in combinations(helper_list,2)
        if issubset(pair[1][2][2],pair[2][2][2]) || issubset(pair[2][2][2],pair[1][2][2])
            if subspace_dim(Field,pair[1][2][1]) + 1 == subspace_dim(Field,pair[2][2][1]) || subspace_dim(Field,pair[2][2][1]) + 1 == subspace_dim(Field,pair[1][2][1])  
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
################################################################################


@doc raw"""
    Are_isom_q_matroids(QM1::Q_Matroid, QM2::Q_Matroid)

    This returns if the two q-matroids are isomorphic.
    
    Here we use the underlying q-matroid lattice and check if the graph are isomorphic. 
"""
function Are_isom_q_matroids(QM1::Q_Matroid, QM2::Q_Matroid)
    indeps_1 = Q_Matroid_Indepentspaces(QM1) 
    deps_1 = Q_Matroid_Depentspaces(QM1)
    lat_1 = Q_Matroid_lattice(QM1,indeps_1,deps_1,"no")
    indeps_2 = Q_Matroid_Indepentspaces(QM2)
    deps_2 = Q_Matroid_Depentspaces(QM2)
    lat_2 = Q_Matroid_lattice(QM2,indeps_2,deps_2,"no")

    return Graphs.Experimental.has_isomorph(lat_1,lat_2)
end


@doc raw"""
    Are_isom_q_matroidsV2(QM1::Q_Matroid, QM2::Q_Matroid, lats=nothing::Union{Nothing,AbstractVector{SimpleGraph}}) 
"""
function Are_isom_q_matroidsV2(QM1::Q_Matroid, QM2::Q_Matroid, lats=nothing::Union{Nothing,AbstractVector{SimpleGraph}})
    
    if isnothing(lats)
        indeps_1 = Q_Matroid_Indepentspaces(QM1) 
        deps_1 = Q_Matroid_Depentspaces(QM1)
        l1 = Q_Matroid_lattice(QM1,indeps_1,deps_1,"no")
        indeps_2 = Q_Matroid_Indepentspaces(QM2)
        deps_2 = Q_Matroid_Depentspaces(QM2)
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
    isom_classes_from_mats(List_matrices::AbstractVector{fqPolyRepMatrix})

    Returns a list of all the different isom.-classes of q-matroids coming from the matrices in the initial input-list.
    
    Note that these are only different isom.-classes of representable q-matroids.

    The list is given in the follwing way: (matrix rep.the class, q-mat of the matrix, length of it's bases, num of elm in the isom.-class) 
"""
function Isom_classes_from_mats(field::fqPolyRepField, list_matrices::AbstractVector{fqPolyRepMatrix})
    unique_index = 1
    matrices_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,matrix) in enumerate(list_matrices)
        QM = q_matroid_from_matrix(field,matrix)
        indeps = Q_Matroid_Indepentspaces(QM)
        deps = Q_Matroid_Depentspaces(QM)
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
    isom_classes_from_matsV2(List_matrices::AbstractVector{fqPolyRepMatrix}) 
"""
function Isom_classes_from_matsV2(field::fqPolyRepField, list_matrices::AbstractVector{fqPolyRepMatrix})
    unique_index = 1
    matrices_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,matrix) in enumerate(list_matrices)
        QM = q_matroid_from_matrix(field,matrix)
        indeps = Q_Matroid_Indepentspaces(QM)
        deps = Q_Matroid_Depentspaces(QM)
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
    isom_classes_from_bases(List_bases::AbstractVector{fpMatrix})

    Returns a list of all the different isom.-classes of q-matroids coming from approved base-tuples in the initial input-list.

    The list is given in the follwing way: (matrix rep.the class, q-mat of the matrix, length of it's bases, num of elm in the isom.-class) 
"""
function Isom_classes_from_bases(field::Nemo.fpField, List_bases::AbstractVector{AbstractVector{fpMatrix}})
    unique_index = 1
    Bases_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,elm) in enumerate(List_bases)
        QM = Q_Matroid(field,elm)
        indeps = Q_Matroid_Indepentspaces(QM)
        deps = Q_Matroid_Depentspaces(QM)
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
    isom_classes_from_basesV2(List_bases::AbstractVector{fpMatrix})
"""
function Isom_classes_from_basesV2(field::Nemo.fpField, List_bases::AbstractVector{AbstractVector{fpMatrix}})
    unique_index = 1
    Bases_dict = OrderedDict([])
    key_value_list = []
    list_diff_q_mat = []    

    # Create dict
    for (id,elm) in enumerate(List_bases)
        QM = Q_Matroid(field,elm)
        indeps = Q_Matroid_Indepentspaces(QM)
        deps = Q_Matroid_Depentspaces(QM)
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
    Q_Matroid_charpoly(QM::Q_Matroid, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix})

    Returns the characteristic-polynimial of the q-matroid.

    We require for this function, the Independent-and Dependent-Spaces, because it's computational faster.
"""
function Q_Matroid_charpoly(QM::Q_Matroid, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix})
    Bases = QM.bases
    Field = QM.field
    dim = ncols(Bases[1])

    # Create polynomial ring over Z
    R,z = polynomial_ring(ZZ,"z")

    # create all subspaces
    all_spaces = sort(all_subspaces(Field,dim), by = x->subspace_dim(Field,x))

    # Compute rank of q-matroid
    #max_space = all_spaces[findall(x-> nrows(x)==dim,all_spaces)][1]
    q_mat_rank = subspace_dim(Field,Bases[1])

    # Search for zero_vec
    zero_vec = all_spaces[1]

    # Create the char-polyn for the given q-matroid
    char_polyn = R(0)
    
    for space in all_spaces
        diff = q_mat_rank-Q_Matroid_Ranks(QM,space,Indeps,Deps)
        char_polyn += Möbius_func_subspace_lat(Field,zero_vec,space)*z^(diff)
    end
     
    return char_polyn
end
################################################################################


@doc raw"""
    Projectivization_matroid(QM::Q_Matroid, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix})

    Returns the projectivization matroid of the given q-matroid.
"""
function Projectivization_matroid(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    dim = ncols(Bases[1])
    q_rank = subspace_dim(Field,Bases[1])
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
        one_subs = dim_one_subs(Field,basis)
        id_sub_pair_list = []
        for (id,value) in groundset_dictionary
            for space in one_subs
                if space == value
                    push!(id_sub_pair_list,(id,value))
                end
            end
        end

        for combi in combinations(id_sub_pair_list,q_rank)
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

    Returns the dual Q-Matroid for the given Q-Matroid w.r.t. the standard dot product. 
"""
# Changes to old version:
# (1) got rid of in-func. varible `Field`
# (2) instatiated the new q-matroid via the groudspace

function Dual_Q_Matroid(QM::Q_Matroid)
    Bases = QM.bases
    bases_dual_q_matroid = AbstractVector{fpMatrix}([])

    for basis in Bases
        dual_basis = orthogonal_complement(basis)[1]
        push!(bases_dual_q_matroid,dual_basis)
    end

    Dual_QM = Q_Matroid(QM.groundspace,bases_dual_q_matroid)

    return Dual_QM
end
################################################################################


@doc raw"""
    Simplyfy_rep_mat(QM::Q_Matroid)

    Given a list of spaces as matrices in RREF, the function searchs for the "id"-matrix which has the most left pivot elements.
"""
function Simplyfy_rep_mat(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    char = Int(characteristic(Field))
    Ext_F = FiniteField(char,1,"a")[1]
    dim = ncols(Bases[1])
    q_rank = subspace_dim(Field,Bases[1])

    if q_rank != 0
        num_vars = dim*q_rank+1

        # Create polynomial ring
        R,x = polynomial_ring(Ext_F,num_vars)
        MS = matrix_space(R,q_rank,dim)
        
        # Create matrix with all zeros 
        G = MS(0)
        pivot_indices = []

        # Search bases for matrices with only num. ones = q_rank
        for basis in Bases
            indices = findall(y->y==1,Array(basis))
            if length(indices) == q_rank
                push!(pivot_indices,indices)
            end
        end

        sort!(pivot_indices)

        # Fill the entries that are already know
        if pivot_indices == []
            return "You input a non q-matroid"
        else
            for cart_index in pivot_indices[1]
                G[cart_index] = R(1)
            end
            
            count = 1
            for pair in combinations(pivot_indices[1],2)
                if Int(pair[1][1]) + 1 == Int(pair[2][1]) 
                    if abs(pair[2][2]-pair[1][2]) >= 2
                        for k in range(2, abs(pair[2][2]-pair[1][2]))
                            G[pair[1][1],pair[1][2]+k-1] = R(x[count])
                            if pair[1][1] != 1
                                for d in range(1,pair[1][1])
                                    G[d,pair[1][2]+k-1] = R(x[count])
                                    count += 1
                                end
                            end
                            count += 1
                        end
                    end
                end
            end

            max_col = pivot_indices[1][length(pivot_indices[1])][2]
            if max_col != dim
                for k in range(max_col+1,dim)
                    for l in range(1,q_rank)
                        G[l,k] = R(x[count])
                        count += 1
                    end
                end
            end

            return G, R, x[num_vars]
        end
    else
        matrix_space(Ext_F,1,dim)
        return MS(0)
    end
    
end


@doc raw"""
    Is_representable_midstep(QM::Q_Matroid, Deps::AbstractVector{fpMatrix}, G::AbstractAlgebra.Generic.MatSpaceElem{fqPolyRepMPolyRingElem}, R::fqPolyRepMPolyRing ,last_var::fqPolyRepMPolyRingElem)

    This function already returns if a given q-matroid is representable or not and also returns the ideal gen by polynomials coming from bases and non-bases.
    
    But we need a lot of input and have to do `Simplyfy_rep_mat` seperatly.
"""
function Is_representable_midstep(QM::Q_Matroid, Deps::AbstractVector{fpMatrix}, G::AbstractAlgebra.Generic.MatSpaceElem{fqPolyRepMPolyRingElem}, R::fqPolyRepMPolyRing ,last_var::fqPolyRepMPolyRingElem)
    Bases = QM.bases
    Field = QM.field
    char = Int(characteristic(Field))
    Ext_F,a = FiniteField(char,1,"a")
    q_rank = subspace_dim(Field,Bases[1])

    if q_rank == 0
        dim = ncols(Bases[1])
        ms = matrix_space(Ext_F,1,dim)

        return "Q-Matroid is not rep'able by $(ms(0))!!"
    else
        q_rank_dep_spaces = []
        for dep_space in Deps
            if subspace_dim(Field,dep_space) == q_rank
                push!(q_rank_dep_spaces,dep_space)
            end
        end

        # Create the polynomials
        gen_polys = []
        bases_polys = []
        rabi_poly = last_var

        for deps in q_rank_dep_spaces
            p = det(G*transpose(matrix(Ext_F,Array(deps))))
            push!(gen_polys,p)
        end
        for basis in Bases
            p = det(G*transpose(matrix(Ext_F,Array(basis))))
            push!(bases_polys,p)
        end

        for poly in bases_polys
            rabi_poly *=poly
        end
        push!(gen_polys,rabi_poly-R(1))

        # Create the ideal and test if it is one
        I = ideal(R,Array(gen_polys))
        gb = collect(groebner_basis(I, ordering = lex(R)))
        I = ideal(R,gb)

        if is_one(I)
            return "Q-Matroid is not rep'able!!", I 
        else
            return "Q-Matroid is rep'able!!", I  
        end
    end

end


@doc raw"""
    Is_representable(QM::Q_Matroid)

    This function returns if a given q-matroid is representable or not and also returns the ideal gen by polynomials coming from bases and non-bases.
    
    It combines the `Simplyfy_rep_mat` and `Is_representable_midstep` function.
"""
function Is_representable(QM::Q_Matroid)

    if subspace_dim(QM.field,QM.bases[1]) == 0
        dim = ncols(QM.bases[1])
        ms = matrix_space(QM.field,1,dim)

        return "Q-Matroid is not rep'able by $(ms(0))!!"
    else
        G,R,var = Simplyfy_rep_mat(QM)
        deps = Q_Matroid_Depentspaces(QM)
        text,I = Is_representable_midstep(QM,deps,G,R,var)

        return text, I
    end
    
end
################################################################################


@doc raw"""
    Are_q_quotients(QM1::Q_Matroid, QM2::Q_Matroid)

    Returns if the given q-matroids happen to be q-quotients.

    This means that every circ of `QM2` is a sum of circ's of `QM1`.
"""
function Are_q_quotients(QM1::Q_Matroid, QM2::Q_Matroid)
    is_q_quotient = true
    Field = QM.field
    circs_1 = Q_Matroid_Circuits(QM1)
    circs_2 = Q_Matroid_Circuits(QM2)

    for circ in circs_2
        circ_counter = 0
        sub_dim = subspace_dim(Field,circ)
        for i in range(1,sub_dim)
            if i == 1
                if circ in circs_1
                    circ_counter += 1
                else
                    continue
                end
            else
                summing_collec = collect(combinations(circs_1,i))
                for tuple in summing_collec
                    for elm in tuple
                        if elm != tuple[1]
                            tuple[1] = sum_vs(Field,tuple[1],elm)
                        end
                    end
                    if tuple[1] == circ
                        circ_counter += 1
                    else
                        continue
                    end
                end
            end
        end
        if circ_counter != 0
            continue
        else
            is_q_quotient = false
            break
        end
    end

    return is_q_quotient
    
end
################################################################################


@doc raw"""
    Is_q_concordant_collec(collection::AbstractVector{Q_Matroid})

    Returns if the given collection of q-matroids is a q-concordant collection.
        
    This means that every pair of distinct q-matroids from that collection are q-quotients (in one way). 
"""
function Is_q_concordant_collec(collection::AbstractVector{Q_Matroid})
    is_q_concordant = true

    for combi in combinations(collection,2)
        if Are_q_quotients(combi[1],combi[2]) || Are_q_quotients(combi[2],combi[1]) 
            continue
        else
            is_q_concordant = false
        end
    end

    return is_q_concordant
end
################################################################################


@doc raw"""
    Q_Higgs_lift(QM1::Q_Matroid, QM2::Q_Matroid)

    Returns the Q-Higgs Lift of the given q-matroids.

    Here it's required that `QM1` is a q-quotient of `QM2`
"""
function Q_Higgs_lift(QM1::Q_Matroid, QM2::Q_Matroid)
    Bases_1 = QM1.bases
    Field = QM1.field
    dim = ncols(Bases_1[1])
    rank_1 = subspace_dim(Field,Bases_1[1])
    ms = matrix_space(Field,1,dim)
    zero_vec = ms(0)
    
    Indeps_1 = Q_Matroid_Indepentspaces(QM1)
    Indeps_2 = Q_Matroid_Indepentspaces(QM2)
    Deps_1 = Q_Matroid_Depentspaces(QM1)
    Q_Higgs_lift_bases = AbstractVector{fpMatrix}([])

    # Construct all subspaces
    all_spaces = all_subspaces(Field,dim)
    
    # Sort the spaces by the rule: a bases of the Q-Q_Higgs_lift is indep. in Q-Mat with Bases_2 and having rank rank_1 in in Q-Mat with Bases_1
    for space in all_spaces
        if space in Indeps_2
            if Q_Matroid_Ranks(QM1,space,Indeps_1,Deps_1) == rank_1
                if subspace_dim(Field,space) == rank_1 + 1
                    if space != zero_vec
                        push!(Q_Higgs_lift_bases,space)
                    end
                end
            end
        end
    end

    return Q_Matroid(Field,Q_Higgs_lift_bases)
end