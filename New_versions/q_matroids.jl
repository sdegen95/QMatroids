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
    Indeps = Q_Matroid_Indepentspaces(QM)

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