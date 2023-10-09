################################################################################
##  Helper-functions for subspaces
################################################################################
using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices
include("./q_properties.jl")

@doc raw"""
    q_binomialcoeff(q::Oscar.IntegerUnion, n::Oscar.IntegerUnion, k::Oscar.IntegerUnion)

    Returns the q-binimoal coefficient.

    This counts the number of subspaces of a vectorspace over a finite field of size `q`.
"""
function q_binomcoeff(q::Oscar.IntegerUnion, n::Oscar.IntegerUnion, k::Oscar.IntegerUnion)
    denom = 1
    num = 1
    for i in range(1,k)
        denom *= q^i-1
        num *= q^(n-i+1)-1
    end
    return Int(num/denom)

end
################################################################################


@doc raw"""
    subspaces_fix_dim(field::Nemo.fpField, k::Oscar.IntegerUnion, n::Oscar.IntegerUnion)

    Returns all subspaces of a fixed dimension `k` in the fixed ambient dimension `n`.
"""
function subspaces_fix_dim(field::Nemo.fpField, k::Oscar.IntegerUnion, n::Oscar.IntegerUnion)
    char = Int(Oscar.characteristic(field))
    one_dims = AbstractVector{fpMatrix}([])
    k_spaces = AbstractVector{fpMatrix}([])

    ms = matrix_space(field,1,n)
    zero_vec = ms(0)

    # Create one dim subspaces
    for i in range(1,char^(n)-1)
        array = [digits(i,base=char,pad=n)]
        vec = matrix(field,array)
        push!(one_dims,vec)
    end

    # Create all higher dimensional spaces
    if k == 0
        push!(k_spaces,zero_vec)
    else
        for combi in combinations(one_dims,k)
            mat = vcat(combi)
            r,rref_mat = rref(mat)
            if r == k
                push!(k_spaces,rref_mat)
            end
        end
    end

    k_spaces = unique(k_spaces) 
    
    return k_spaces
end
################################################################################


@doc raw"""
    all_subspaces(field::Nemo.fpField, n::Oscar.IntegerUnion)

    Returns all subspaces of the fixed ambient dimension `n`.
"""
function all_subspaces(field::Nemo.fpField, n::Oscar.IntegerUnion)
    all_subs = AbstractVector{fpMatrix}([])

    for i in range(0,n)
        subs = subspaces_fix_dim(field,i,n)
        for sub in subs
            push!(all_subs,sub)
        end
    end

    return all_subs
    
end
################################################################################


@doc raw"""
    subspace_dim(field::Nemo.fpField, space::fqMatrix)

    Returns the dimension of the `space` in an ambient vectorspace.
"""
function subspace_dim(field::Nemo.fpField, space::fpMatrix)
    dim = ncols(space)
    ms = matrix_space(field,1,dim)
    zero_vec = ms(0)

    if space == zero_vec
        return 0
    else 
        return nrows(space)
    end
    
end
################################################################################


@doc raw"""
    sum_vs(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)

    Returns the vs-sum of the two subspaces `space_1` `space_2` sitting in an ambient vectorspace.
"""
function sum_vs(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)
    Ms = matrix_space(field,1,ncols(space_1))
    zero_vec = Ms(0)

    New_mat = vcat(space_1,space_2)
    r,rref_mat = rref(New_mat)

    # cleaning zero rows
    C = []
    for i in range(1,nrows(rref_mat))
        if rref_mat[i,:] != zero_vec
            push!(C,rref_mat[i,:])
        end
    end
    cleaned_mat = vcat(collect(combinations(C,length(C)))[1])

    if cleaned_mat == []
        return zero_vec
    else
        return cleaned_mat
    end
end
################################################################################


@doc raw"""
    subspace_set(field::Nemo.fpField, space::fpMatrix)

    Returns the set of elements of the subspaces `space` sitting in an ambient vectorspace.
"""
function subspace_set(field::Nemo.fpField, space::fpMatrix)
    subs_set = Set{fpMatrix}([])
    one_dims = []
    dim = subspace_dim(field,space)
    char = Int(characteristic(field)) 
    
    if dim != 0
        # Create all vec of size dim 
        for i in range(0,char^(dim)-1)
            array = [digits(i,base=char,pad=dim)]
            vec = matrix(field,array)
            push!(one_dims,vec)
        end

        for elm in one_dims
            prod = elm*space
            push!(subs_set,prod)
        end

    elseif dim == 0
        Ms = matrix_space(field,1,ncols(space))
        zero_vec = Ms(0)
        push!(subs_set,zero_vec)
    end

    return subs_set
    
end
################################################################################

@doc raw"""
    subspaces_fix_space(field::Nemo.fpField, space::fpMatrix)

    Returns all subspaces of fixed `space` sitting in an ambient vectorspace.
"""
function subspaces_fix_space(field::Nemo.fpField, space::fpMatrix)
    Ms = matrix_space(field,1,ncols(space))
    zero_vec = Ms(0)
    collection_subspaces = AbstractVector{AbstractVector{fpMatrix}}([])
    zero_spaces = AbstractVector{fpMatrix}([zero_vec])
    one_spaces = AbstractVector{fpMatrix}([])
    dim = subspace_dim(field,space)

    # Create 1-spaces
    S = subspace_set(field,space)
    for x in S
        if x != zero_vec
            push!(one_spaces,x)
        end
    end

    if dim == 0
        push!(collection_subspaces,zero_spaces)
    elseif dim != 0
        push!(collection_subspaces,zero_spaces)
        push!(collection_subspaces,one_spaces)
        if dim >= 2
            for i in range(2,dim)
                i_spaces = AbstractVector{fpMatrix}([])
                for combi in combinations(one_spaces,i)
                    mat = vcat(combi)
                    r, rref_mat = rref(mat)
                    if r == i
                        push!(i_spaces,rref_mat)
                    end
                end
                i_spaces = unique(i_spaces)
                push!(collection_subspaces,i_spaces)
            end
        end
    end

    return collection_subspaces


end
################################################################################


@doc raw"""
    containments_fix_space(field::Nemo.fpField, space::fpMatrix)

    Returns all spaces that contains a fixed `space` sitting in an ambient vectorspace.
"""
function containments_fix_space(field::Nemo.fpField, space::fpMatrix)
    all_higher_spaces = []
    spaces_containing_space = AbstractVector{fpMatrix}([])
    dim = ncols(space)
    sub_dim = subspace_dim(field,space)

    my_space_set = subspace_set(field,space)

    # Push in the space it self
    push!(spaces_containing_space,space)

    # Create all higher dim spaces
    for i in range(sub_dim+1,dim)
        subs = subspaces_fix_dim(field,i,dim)
        for sub in subs
            push!(all_higher_spaces,[sub,subspace_set(field,sub)])
        end
    end

    # Create list of all higher dim spaces containing that space
    for pair in all_higher_spaces
        if issubset(my_space_set,pair[2])
            push!(spaces_containing_space,pair[1])
        else
            continue
        end
    end

    return spaces_containing_space
end
################################################################################