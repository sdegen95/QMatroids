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
function Q_Matroid_Indepentspaces(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field

    q_mat_indep_spaces = AbstractVector{fpMatrix}([])
    for basis in Bases
        basis_subspaces = subspaces_fix_space(Field,basis)
        for arr in basis_subspaces
            for elm in arr
                push!(q_mat_indep_spaces,elm)
            end
        end
    end

    q_mat_indep_spaces = sort(unique!(q_mat_indep_spaces), by =  x -> subspace_dim(Field, x))
    
    return q_mat_indep_spaces
    
end
################################################################################


@doc raw"""
    Q_Matroid_Depentspaces(QM::Q_Matroid)

    This returns the Depentspaces of the Q-Matroid.
"""
function Q_Matroid_Depentspaces(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    dim = ncols(Bases[1])
    q_mat_dep_spaces = AbstractVector{fpMatrix}([])
    all_subs = all_subspaces(Field,dim)

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
function Q_Matroid_Loopspace(QM::Q_Matroid)
    Field = QM.field
    Deps = Q_Matroid_Depentspaces(QM)

    if Deps != []
        min_dim = minimum(y->subspace_dim(Field,y),Deps)
        if min_dim == 1 
            return AbstractVector{fpMatrix}([x for x in Deps[findall(y->subspace_dim(Field,y)==min_dim,Deps)]])
        else
            return []
        end
    else
        return []
    end
    
end
################################################################################


@doc raw"""
    Q_Matroid_Ranks(QM::Q_Matroid, Space::fpMatrix, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix})

    This returns the rank of a specific space in a given q-matroid.
    
    We require for this function, the Independent-and Dependent-Spaces, because it's computational faster.
"""
function Q_Matroid_Ranks(QM::Q_Matroid, Space::fpMatrix, Indeps::AbstractVector{fpMatrix}, Deps::AbstractVector{fpMatrix})
    Field = QM.field

    # Convert a space not in rref in rref space
    r,New_space = rref(Space)

    New_space_set = subspace_set(Field,New_space)
    indep_spaces_in_New_Space = []

    if New_space in Indeps
        return subspace_dim(Field,New_space)

    elseif New_space in Deps
        for indep_space in Indeps
            if issubset(subspace_set(Field,indep_space),New_space_set)
                push!(indep_spaces_in_New_Space,indep_space)
            end
        end

        if subspace_dim(Field,New_space) == 1
            return 0
        else
            if length(indep_spaces_in_New_Space) == 1
                return 0
            else
                return maximum(y->subspace_dim(Field,y),indep_spaces_in_New_Space)
            end
        end
    end
end
################################################################################


@doc raw"""
    Q_Matroid_Circuits(QM::Q_Matroid)

    This returns the circuits of the q-matroid.
"""
function Q_Matroid_Circuits(QM::Q_Matroid)
    Field = QM.field
    Indeps = Q_Matroid_Indepentspaces(QM)
    Deps = Q_Matroid_Depentspaces(QM)
    q_mat_circuits = AbstractVector{fpMatrix}([])
    not_correct_spaces = []

    for dep_space in Deps
        loop_breaker = true
        arrays_subs = subspaces_fix_space(Field,dep_space)
        deleteat!(arrays_subs,subspace_dim(Field,dep_space)+1)
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
################################################################################


@doc raw"""
    Is_paving_q_matroid(QM::Q_Matroid)

    This returns the circuits of the q-matroid.
"""
function Is_paving_q_matroid(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    right_ones = []
    q_rank = subspace_dim(Field, Bases[1])
    Circuits = Q_Matroid_Circuits(QM)

    for circ in Circuits
        if  subspace_dim(Field,circ) >= q_rank
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
################################################################################