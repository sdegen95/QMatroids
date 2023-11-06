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
    Construct a `q-matroid` with bases and field attribute.

    All matrices in the bases-list need to be in RREF.
"""

struct Q_Matroid
    field::Nemo.fpField           # field of the groudspace
    bases::AbstractVector{fpMatrix} # bases of the q-matroid
end

function Base.show(io::IO, QM::Q_Matroid)
    q_rank = subspace_dim(QM.field,QM.bases[1])
    dim = ncols(QM.bases[1])
    print(io, "Q-Matroid of rank $(q_rank) in $(dim)-dim. vector-space over the $(QM.field)")
end
################################################################################


@doc raw"""
    q_matroid_from_independentspaces(field::Nemo.fpField, Indeps::AbstractVector{FpMatrix},choice=nothing::Union{Nothing,String})

    Construct a `q-matroid` from the independentspaces. 

    All matrices in that list need to be in RREF.
"""
function q_matroid_from_independentspaces(field::Nemo.fpField, Indeps::AbstractVector{fpMatrix},choice=nothing::Union{Nothing,String})
    sort!(Indeps, by = x -> subspace_dim(field,x))
    Sorted_indeps = Indeps[findall(y->subspace_dim(field,y)==maximum(z->subspace_dim(field,z),Indeps),Indeps)]
    bases = AbstractVector{fpMatrix}([x for x in Sorted_indeps])

    if isnothing(choice)
        return Q_Matroid(field,bases)
    elseif choice == "yes"
        return bases
    end
    
end
################################################################################


@doc raw"""
    q_matroid_from_matrix(field::fqPolyRepField, Mat::fqPolyRepMatrix)

    Construct a `q-matroid` from a Matrix that represents it.
"""
function q_matroid_from_matrix(field::fqPolyRepField, Mat::fqPolyRepMatrix)
    n = ncols(Mat)
    Ms = matrix_space(field,1,n)
    zero_vec = Ms(0)
    q_mat_bases = AbstractVector{fpMatrix}([])

    char = Int(characteristic(field))
    new_field = GF(char)

    if Mat == zero_vec
        k = 0
    else 
        k = nrows(Mat)
    end

    # List of subspaces of dim k which are bases for given G
    subs = subspaces_fix_dim(new_field,k,n)
    for sub in subs
        mat_product = Mat*transpose(sub)
        if rank(mat_product) == k
            push!(q_mat_bases,sub)
        end
    end

    return Q_Matroid(new_field,q_mat_bases)
    
end
################################################################################



@doc raw"""
    Are_q_matroid_dependentspaces(field::Nemo.fpField, Deps::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})

    Returns if the inputed list of spaces form the set of Depnedentspaces of a Q-Matroid.

    For the choice you can choose "yes" and if the list is not the set of Depnedentspaces of a Q-Matroid, it will return also which axiom of (D1)-(D3) fails. 
"""
function Are_q_matroid_dependentspaces(field::Nemo.fpField, Deps::AbstractVector{fpMatrix}, choice=nothing::Union{Nothing,String})
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

        # Fill info_dict with all necesssary information
        for (id,space) in enumerate(Deps)
            merge!(deps_dict,Dict(id=>[space,containments_fix_space(field,space)]))
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
                    if !(inters_vs(field,pair[1][1],pair[2][1])[1] in Deps)
                        sum = sum_vs(field,pair[1][1],pair[2][1])
                        codim_ones = codim_one_subs(field,sum)
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