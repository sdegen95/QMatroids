################################################################################
##  Constructing
################################################################################
using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices

###########################################################################################
# !!! All matrices, in any list or alone, you input in a function/method should be RREF !!!
###########################################################################################


@doc raw"""
    Construct a `q-matroid` with bases and groundspace attribute.

    All matrices in the bases-list need to be in RREF.
"""
# Changes to old version:
# (1) replaced `field`-attribute by `groundspace`-attribute 

struct Q_Matroid
    groundspace::fpMatrix           # groudspace as id-matrix over the corresponding field.
    bases::AbstractVector{fpMatrix} # bases of the q-matroid.
end

# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) using new attribute `groundspace`

function Base.show(io::IO, QM::Q_Matroid)
    q_rank = rank(QM.bases[1])
    dim = ncols(QM.groundspace)
    print(io, "Q-Matroid of rank $(q_rank) in $(dim)-dim. vector-space over the $(base_ring(QM.bases[1]))")
end
################################################################################


@doc raw"""
    q_matroid_from_independentspaces(Indeps::AbstractVector{fpMatrix}, show_bases=false::Bool)

    Construct a `q-matroid` from the independentspaces.
    
    One can set the default-value for `show_bases` from `false` to `true`, to only show the bases of the resulting q-matroid.

    All matrices in that list need to be in RREF.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable
# (3) changed `choice`-var. to `show_bases`-var. (boolean value) with default `false`.
# (4) using `base_ring`-func. instead of `field`-func.-variable
# (5) using the new attribute of the q-matroid struct

function q_matroid_from_independentspaces(Indeps::AbstractVector{fpMatrix}, show_bases=false::Bool)   
    field = base_ring(Indeps[1])
    dim = ncols(Indeps[1])
    id_mat = matrix_space(field,dim,dim)(1)

    sort!(Indeps, by = x -> rank(x))

    max_dim_spaces_indices = findall(y->rank(y)==maximum(z->rank(z),Indeps),Indeps)
    Sorted_indeps = Indeps[max_dim_spaces_indices]                                  
    bases = AbstractVector{fpMatrix}([x for x in Sorted_indeps])

    if show_bases == false
        return Q_Matroid(id_mat,bases) 
    elseif show_bases == true
        return bases
    end
    
end
################################################################################


@doc raw"""
    q_matroid_from_matrix(Mat::fqPolyRepMatrix)

    Construct a `q-matroid` from a Matrix that represents it.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable
# (3) using `base_ring`-func. instead of `field`-func.-variable
# (4) got rid of if-statement to determine `k` 
# (5) using the new attribute of the q-matroid struct 

function q_matroid_from_matrix(Mat::fqPolyRepMatrix)
    field = base_ring(Mat) 
    n = ncols(Mat)
    k = rank(Mat) 
    char = Int(characteristic(field))
    new_field = GF(char)
    id_mat = matrix_space(new_field,n,n)(1)

    q_mat_bases = AbstractVector{fpMatrix}([])
    # List of subspaces of dim k which are bases for given G
    subs = subspaces_fix_dim(new_field,k,n)
    for sub in subs
        mat_product = Mat*transpose(sub)
        if rank(mat_product) == k
            push!(q_mat_bases,sub)
        end
    end

    return Q_Matroid(id_mat,q_mat_bases)
    
end
################################################################################


@doc raw"""
    Uniform_q_matroid(k::IntegerUnion, n::IntegerUnion)

    Constructs the `uniform q-matroid` of rank `k` in dimension `n`.
"""
# Changes to old version:
# there is no old version 

function Uniform_q_matroid(field::Nemo.fpField ,k::Oscar.IntegerUnion, n::Oscar.IntegerUnion)
    all_k_spaces = subspaces_fix_dim(field,k,n)
    gs = matrix_space(field,n,n)(1)

    return Q_Matroid(gs,all_k_spaces)
end


@doc raw"""
    Are_q_matroid_dependentspaces(field::Nemo.fpField, Deps::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})

    Returns if the inputed list of spaces form the set of Depnedentspaces of a Q-Matroid.

    For the choice you can choose "yes" and if the list is not the set of Depnedentspaces of a Q-Matroid, it will return also which axiom of (D1)-(D3) fails. 
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

# field-var def via first elm in `Deps`-list: possible issue if this list is empty

function Are_q_matroid_dependentspaces(Deps::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})
    field = base_ring(Deps[1])
    are_deps = true
    loop_breaker = true
    fail = "Non"

    if Deps == []
        if isnothing(choice)
            return are_deps
        elseif choice == "Yes"
            return are_deps,fail
        end
    else
        dim = ncols(Deps[1])
        ms = matrix_space(field,1,dim)
        zero_vec = ms(0)
        deps_dict = OrderedDict([])
        vs_sums = []

        # Fill info_dict with all necesssary information
        for (id,space) in enumerate(Deps)
            merge!(deps_dict,Dict(id=>[space,containments_fix_space(space)]))
        end

        # Check axiom (D1)
        if zero_vec in Deps
            are_deps = false
            fail = "Axiom (D1)"
        end

        # Check axiom (D2)
        if are_deps
            for pair in values(deps_dict)
                if issubset(pair[2],Deps) == false
                    are_deps = false
                    fail = "Axiom (D2)"
                    break
                else
                    continue
                end
            end
        end

        # Check axiom (D3)
        if are_deps
            for pair in combinations(collect(values(deps_dict)),2)
                if loop_breaker
                    if !(inters_vsV3(pair[1][1],pair[2][1]) in Deps)
                        sum = sum_vsV2(pair[1][1],pair[2][1])
                        if !(sum in vs_sums)
                            push!(vs_sums,sum)
                            codim_ones = codim_one_subs(sum)
                            for space in codim_ones
                                if !(space in Deps)
                                    are_deps = false
                                    loop_breaker = false
                                    fail = "Axiom (D3)"
                                    break
                                else
                                    continue
                                end
                            end
                        else
                            continue
                        end
                    else
                        continue
                    end
                else
                    break
                end
            end
        end

        if isnothing(choice)
            return are_deps
        elseif choice == "Yes"
            return are_deps,fail
        end
    end

end
################################################################################


@doc raw"""
    Are_q_matroid_hyperplanes(Hyperp::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})

    Returns if the inputed list of spaces form the set of Hyperplanes of a Q-Matroid.

    For the choice you can choose "yes" and if the list is not the set of Hyperplanes of a Q-Matroid, it will return also which axiom of (H1)-(H3) fails.
"""
# Changes to old version:
# There is no old version

# field-var def via first elm in `Deps`-list: possible issue if this list is empty

function Are_q_matroid_hyperplanes(Hyperps::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})

    if Hyperps == []
        if isnothing(choice)
            return true
        elseif choice == "Yes"
            return true, "Non"
        end
    else
        Hyperps = sort(Hyperps,by = x -> rank(x))
        field = base_ring(Hyperps[1])
        are_hyperps = true
        fail = "Non"

        dim = ncols(Hyperps[1])
        id_mat = matrix_space(field,dim,dim)(1)

        # Check Axiom (H1)
        if id_mat in Hyperps
            are_hyperps = false
            fail = "Axiom (H1)"
        end

        # Check Axiom (H2)
        Hyperps_sets = sort([subspace_set(space) for space in Hyperps],by = x->length(x))
        if are_hyperps
            for combi in combinations(Hyperps_sets,2)
                if length(combi[1]) != length(combi[2])
                    if issubset(combi[1],combi[2])
                        are_hyperps = false
                        fail = "Axiom (H2)"
                        break
                    end
                end
            end
        end
        
        # Check Axiom (H3)
        if are_hyperps
            one_spaces = subspaces_fix_dim(field,1,dim)
            loop_breaker = false
            for combi in combinations(Hyperps,2)
                if !(loop_breaker)
                    inters = inters_vsV3(combi[1],combi[2])
                    for one_sp in one_spaces
                        sum = sum_vsV2(inters,one_sp)
                        sum_set = subspace_set(sum)
                        count = 0
                        for set in Hyperps_sets
                            if issubset(sum_set,set)
                                count += 1
                            end
                        end
                        if count == 0
                            are_hyperps = false
                            loop_breaker = true
                            fail = "Axiom (H3)"
                            break
                        end
                    end
                else
                    break
                end
            end
        end

        if isnothing(choice)
            return are_hyperps
        elseif choice == "Yes"
            return are_hyperps,fail
        end
    end

end
################################################################################


@doc raw"""
    Are_q_matroid_bases(Bases::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})

    Returns if the inputed list of spaces form the set of Bases of a Q-Matroid.

    The `Bases`-List has to contain at least one element and all its elements should have the same dimension.
"""
# Changes to old version:
# There is no old version

# field-var def via first elm in `Deps`-list: possible issue if this list is empty

function  Are_q_matroid_bases(Bases::AbstractVector{fpMatrix})
    field = base_ring(Bases[1])
    dim = ncols(Bases[1])
    q_rank = rank(Bases[1])

    if Set(Bases) == Set(Uniform_q_matroid(field,q_rank,dim).bases)
        return true
    else
        E = matrix_space(field,dim,dim)(1)
        are_bases = true

        # Get all codim 1 spaces of E
        codim_ones_E = codim_one_subs(E)
        Dict_codim_one_E = OrderedDict([id=>[space,subspace_set(space)] for (id,space) in enumerate(codim_ones_E)])
        
        # Get all codim 1 spaces of all elements in Bases
        Info_dict_bases = OrderedDict([])
        for (id,space) in enumerate(Bases)
            codim_ones = codim_one_subs(space)
            list = [[x,subspace_set(x)] for x in codim_ones]
            merge!(Info_dict_bases,Dict([id=>[space,subspace_set(space),list]]))
        end

        # Get all one spaces
        one_spaces = subspaces_fix_dim(field,1,dim)
        Dict_one_spaces = OrderedDict([id=>[space,subspace_set(space)] for (id,space) in enumerate(one_spaces)])
        
        # Check (nB3) for B_1=B_2
        loop_breaker = true
        for pair in Info_dict_bases
            if loop_breaker
                for elm in pair[2][3]
                    count = 0
                    for tuple in Dict_codim_one_E
                        if count != 0
                            break
                        else
                            if issubset(elm[2],tuple[2][2]) && !(issubset(pair[2][2],tuple[2][2]))
                                counter = 0
                                for arr in Dict_one_spaces
                                    if !(issubset(arr[2][2],tuple[2][2]))
                                        sum = sum_vsV2(elm[1],arr[2][1])
                                        if !(sum in Bases)
                                            counter +=1
                                            break
                                        end
                                    end
                                end
                                if counter == 0
                                    count +=1
                                end
                            end
                        end
                    end
                    if count == 0
                        are_bases = false
                        loop_breaker = false
                        break
                    end
                end
            else
                break
            end
        end

        if are_bases

        # Check (nB3) for distinct B_1, B_2
            loop_breaker = true
            for pair in combinations(Info_dict_bases,2)
                if loop_breaker
                    for elm in pair[1][3]
                        count = 0
                        for tuple in Dict_codim_one_E
                            if count != 0
                                break
                            else
                                if issubset(elm[2],tuple[2][2]) && !(issubset(pair[2][2],tuple[2][2]))
                                    counter = 0
                                    for arr in Dict_one_spaces
                                        if !(issubset(arr[2][2],tuple[2][2]))
                                            sum = sum_vsV2(elm[1],arr[2][1])
                                            if !(sum in Bases)
                                                counter +=1
                                                break
                                            end
                                        end
                                    end
                                    if counter == 0
                                        count +=1
                                    end
                                end
                            end
                        end
                        if count == 0
                            are_bases = false
                            loop_breaker = false
                            break
                        end
                    end
                else
                    break
                end
            end

            if are_bases
            
            # Symmeric Cases
                loop_breaker = true
                for pair in combinations(Info_dict_bases,2)
                    if loop_breaker
                        for elm in pair[2][3]
                            count = 0
                            for tuple in Dict_codim_one_E
                                if count != 0
                                    break
                                else
                                    if issubset(elm[2],tuple[2][2]) && !(issubset(pair[1][2],tuple[2][2]))
                                        counter = 0
                                        for arr in Dict_one_spaces
                                            if !(issubset(arr[2][2],tuple[2][2]))
                                                sum = sum_vsV2(elm[1],arr[2][1])
                                                if !(sum in Bases)
                                                    counter +=1
                                                    break
                                                end
                                            end
                                        end
                                        if counter == 0
                                            count +=1
                                        end
                                    end
                                end
                            end
                            if count == 0
                                are_bases = false
                                loop_breaker = false
                                break
                            end
                        end
                    else
                        break
                    end
                end
                return are_bases
            else
                return are_bases
            end
        else
            return are_bases
        end
    end

end



################################################################################
# Restriction/Contraction section
################################################################################


@doc raw"""
    Construct a `Embedded_q_matroid` with em_bases, em_groundspace  attribute.
    One can see this as a lower dimensional q-matroid embedded in to the ambient space.
    Note: this itself is not enough to give an ambient-space dimensional q-matroid.


    All matrices in the bases-list need to be in RREF.
"""
# Changes to old version:
# There is no old version 

struct Embedded_q_Matroid
    em_groundspace::fpMatrix           
    em_bases::AbstractVector{fpMatrix}
end

function Base.show(io::IO, EQM::Embedded_q_Matroid)
    q_rank = rank(EQM.em_bases[1])
    dim = rank(EQM.em_groundspace)
    ambient_dim = ncols(EQM.em_groundspace)
    print(io, "Embbeded q-Matroid of dim. $(dim) and rank $(q_rank) in $(ambient_dim)-dim. vector-space over the $(base_ring(EQM.em_groundspace))")
end
################################################################################


@doc raw"""
    Restriction_Q_Matroid(QM::Q_Matroid, restriction_space::fpMatrix)

    Returns the restriction Q-Matroid to a specified space for the given Q-Matroid.
    Note: We do not project here, meaning that the result is a `Embedded q-matroid` in the original space. 
"""
# Changes to old version:
# There is no old version

function Restriction_Q_Matroid(QM::Q_Matroid, restriction_space::fpMatrix)
    Indeps = Q_Matroid_Independentspaces(QM)

    # Compute the subspaces of the given `restriction_space` and rembember all independnet ones
    Subs_lists = subspaces_fix_space(restriction_space) 
    Indeps_restriction_space = AbstractVector{fpMatrix}([])
    for elm in Subs_lists
        for x in elm
            if x in Indeps
                push!(Indeps_restriction_space,x)
            end
        end
    end

    # Compute the bases
    max_dim_spaces_indices = findall(y->rank(y)==maximum(z->rank(z),Indeps_restriction_space),Indeps_restriction_space)
    Sorted_indeps = Indeps_restriction_space[max_dim_spaces_indices]                                  
    Bases_restriction_space = AbstractVector{fpMatrix}([x for x in Sorted_indeps])

    return Embedded_q_Matroid(restriction_space,Bases_restriction_space)

end
################################################################################