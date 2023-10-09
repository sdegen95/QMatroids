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
    q_matroid_from_independentspaces(field::Nemo.fpField, Indeps::AbstractVector{FpMatrix})

    Construct a `q-matroid` from the independentspaces. 

    All matrices in that list need to be in RREF.
"""
function q_matroid_from_independentspaces(field::Nemo.fpField, Indeps::AbstractVector{fpMatrix})
    ms = matrix_space(field,1,ncols(Indeps[1]))
    zero_vec = ms(0)
    sort!(Indeps, by = x -> nrows(x))
    Sorted_indeps = Indeps[findall(y->nrows(y)==maximum(nrows,Indeps),Indeps)]
    bases = [x for x in Sorted_indeps if x!=zero_vec]

    return Q_Matroid(field,bases)
    
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