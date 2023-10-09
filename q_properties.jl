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

    This returns the Loopspace a the q-matroid.
"""
function Q_Matroid_Loopspace(QM::Q_Matroid)
    Field = QM.field
    Deps = Q_Matroid_Depentspaces(QM)

    if Deps != []
        ms = matrix_space(Field,1,nrows(Deps[1]))
        zero_vec = ms(0)
        min_dim = minimum(nrows,Deps)
        if min_dim == 1 
            return AbstractVector{fpMatrix}([x for x in Deps[findall(y->subspace_dim(QM.field,y)==min_dim,Deps)] if x!=zero_vec])
        else
            return []
        end
    else
        return []
    end
    
end
################################################################################


