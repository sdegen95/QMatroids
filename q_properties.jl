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
    Q_Matroid_Flats(QM::Q_Matroid)

    This returns the flats of the q-matroid.
"""
function Q_Matroid_Flats(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    indeps = Q_Matroid_Indepentspaces(QM)
    deps =  Q_Matroid_Depentspaces(QM)

    n = ncols(Bases[1])
    one_spaces = subspaces_fix_dim(Field,1,n)
    all_spaces = all_subspaces(Field,n)
    not_correct_spaces = []
    q_matroid_flats = AbstractVector{fpMatrix}([])

    for space in all_spaces
        one_subs = dim_one_subs(Field,space)
        for one_space in one_spaces
            if !(one_space in one_subs)
                sum = sum_vs(Field,space,one_space)
                if  Q_Matroid_Ranks(QM,sum,indeps,deps) > Q_Matroid_Ranks(QM,space,indeps,deps)
                    continue
                else
                    push!(not_correct_spaces,space)
                    break
                end
            end
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
    Q_Matroid_Spanningspaces(QM::Q_Matroid)

    This returns the flats of the q-matroid.
"""
function Q_Matroid_Spanningspaces(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    q_rank = subspace_dim(Field,Bases[1]) 
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
function Dual_Q_Matroid(QM::Q_Matroid)
    Bases = QM.bases
    Field = QM.field
    bases_dual_q_matroid = AbstractVector{fpMatrix}([])

    for basis in Bases
        dual_basis = orthogonal_complement(Field,basis)[1]
        push!(bases_dual_q_matroid,dual_basis)
    end

    Dual_QM = Q_Matroid(Field,bases_dual_q_matroid)

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