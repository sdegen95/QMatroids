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

###########################################################################################
# !!! All matrices, in any list or alone, you input in a function/method should be RREF !!!
###########################################################################################

@doc raw"""
    q_binomialcoeff(q::Oscar.IntegerUnion, n::Oscar.IntegerUnion, k::Oscar.IntegerUnion)

    Returns the q-binimoal coefficient.

    This counts the number of subspaces of a vectorspace over a finite field of size `q`.
"""
# Changes to old version:
# None

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

    Here `k` has to be an integer between 0 and `n`.
"""
# Changes to old version:
# (1) changed to if-else-statement s.t. the `one_dims` will only be computeted if `0 < k < n`

function subspaces_fix_dim(field::Nemo.fpField, k::Oscar.IntegerUnion, n::Oscar.IntegerUnion)
    char = Int(Oscar.characteristic(field))
    one_dims = AbstractVector{fpMatrix}([])
    k_spaces = AbstractVector{fpMatrix}([])

    ms = matrix_space(field,n,n)
    zero_vec = ms(0)[1,:]
    id_mat = ms(1)

    if k == 0
        push!(k_spaces,zero_vec)
    elseif k == n
        push!(k_spaces,id_mat)
    else
        # Create one dim subspaces
        for i in range(1,char^(n)-1)
            array = [digits(i,base=char,pad=n)]
            vec = rref(matrix(field,array))[2]
            push!(one_dims,vec)
        end
        one_dims = unique(one_dims)

        # Create all higher dimensional spaces
        for combi in combinations(one_dims,k)
            mat = vcat(combi)
            r,rref_mat = rref(mat)
            if r == k
                push!(k_spaces,rref_mat)
            end
        end
        k_spaces = unique(k_spaces)
    end 
    
    return k_spaces
end
################################################################################


@doc raw"""
    all_subspaces(field::Nemo.fpField, n::Oscar.IntegerUnion)

    Returns all subspaces of the fixed ambient dimension `n`.
"""
# Changes to old version:
# None

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
# Changes to old version:
# delete this function

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
    sum_vs(space_1::fpMatrix, space_2::fpMatrix)

    Returns the vs-sum of the two subspaces `space_1` `space_2` sitting in an ambient vectorspace.
"""
# Changes to old version:
# (1) got rid of `field`-variable

function sum_vs(space_1::fpMatrix, space_2::fpMatrix)
    field = base_ring(space_1)
    zero_vec = matrix_space(field,1,ncols(space_1))(0)

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


@doc raw"""
    sum_vsV2(space_1::fpMatrix, space_2::fpMatrix)
"""
# Completely new version

function sum_vsV2(space_1::fpMatrix, space_2::fpMatrix)

    New_mat = vcat(space_1,space_2)
    r,rref_mat = rref(New_mat)

    if r == 0
        return space_1
    else
        return rref_mat[1:r,:]
    end
end


@doc raw"""
    multisum_vs(spaces::AbstractVector{fpMatrix})

    Returns the vs-sum of all subspaces in the list `spaces` sitting in an ambient vectorspace.
"""
# Changes to old version:
# There is no old version

function multisum_vs(spaces::AbstractVector{fpMatrix})
    New_mat = vcat(spaces)
    r,rref_mat = rref(New_mat)

    if r == 0
        return spaces[1]
    else
        return rref_mat[1:r,:]
    end
end
################################################################################


@doc raw"""
    inters_vs(space_1::fpMatrix, space_2::fpMatrix)

    Returns the vs-intersection of the two subspaces `space_1` `space_2` sitting in an ambient vectorspace.
"""
# Changes to old version:
# (1) got rid of `field`-variable
# (2) using rank instead of `subspace_dim`-func
# (3) got rid of the `matrix_space`, `dim` and `zero_vec` in-func. variables

function inters_vs(space_1::fpMatrix, space_2::fpMatrix)

    subs_1 = subspaces_fix_space(space_1)
    subs_2 = subspaces_fix_space(space_2)

    subs_list_1 = []
    subs_list_2 = []

    # Create list ob subs
    for elm in subs_1
        for space in elm
            push!(subs_list_1,space)
        end
    end

    for elm in subs_2
        for space in elm
            push!(subs_list_2,space)
        end
    end

    # Compute intersecton of subs_list_1, subs_list_2
    inters_list = intersect(subs_list_1,subs_list_2)

    # Choose the element with maximal dim in that List
    inters = AbstractVector{fpMatrix}([y for y in inters_list[findall(x->rank(x)==maximum(z->rank(z),inters_list),inters_list)]])

    return inters[1]
end


@doc raw"""
    inters_vsV2(space_1::fpMatrix, space_2::fpMatrix)
"""
# Completly new version

function inters_vsV2(space_1::fpMatrix, space_2::fpMatrix)
    set_space_1 = subspace_set(space_1)
    set_space_2 = subspace_set(space_2)

    inters = AbstractVector{fpMatrix}([elm for elm in intersect(set_space_1,set_space_2)])
    r,new_space= rref(vcat(inters))

    if length(inters) != 1
        return new_space[1:r,:]
    else
        return inters[1]
    end
end


@doc raw"""
    inters_vsV3(space_1::fpMatrix, space_2::fpMatrix)
"""
# Completly new version using kernels

function inters_vsV3(space_1::fpMatrix, space_2::fpMatrix)
    # Compute the kernels of both spaces
    ker_space_1 = transpose(right_kernel(space_1)[2])
    ker_space_2 = transpose(right_kernel(space_2)[2])

    # Glue them and compute the kernel
    intermid_mat = vcat(ker_space_1,ker_space_2)
    r, intersspace = rref(transpose(right_kernel(intermid_mat)[2]))

    # Distinguish between 0-rank and others

    if r == 0
        return intersspace[1,:]
    else
        return intersspace[1:r,:]
    end

end
################################################################################


@doc raw"""
    subspace_set(space::fpMatrix)

    Returns the set of elements of the subspaces `space` sitting in an ambient vectorspace.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function subspace_set(space::fpMatrix)
    field = base_ring(space)
    char = Int(characteristic(field)) 
    sub_dim = rank(space)
    dim = ncols(space)

    subs_set = Set{fpMatrix}([])
    one_dims = []
    
    if sub_dim != 0
        # Create all vec of size sub_dim 
        for i in range(0,char^(sub_dim)-1)
            array = [digits(i,base=char,pad=sub_dim)]
            vec = matrix(field,array)
            push!(one_dims,vec)
        end

        for elm in one_dims
            prod = elm*space
            push!(subs_set,prod)
        end

    elseif sub_dim == 0
        Ms = matrix_space(field,1,dim)
        zero_vec = Ms(0)
        push!(subs_set,zero_vec)
    end

    return subs_set
    
end
################################################################################

@doc raw"""
    subspaces_fix_space(space::fpMatrix)

    Returns all subspaces of fixed `space` sitting in an ambient vectorspace.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable
# (3) changed to if-else-statement s.t. the `one_dims` will only be computeted if `0 < sub_dim`

function subspaces_fix_space(space::fpMatrix)
    field = base_ring(space)
    sub_dim = rank(space)
    zero_vec = matrix_space(field,1,ncols(space))(0)

    collection_subspaces = AbstractVector{AbstractVector{fpMatrix}}([])
    zero_spaces = AbstractVector{fpMatrix}([zero_vec])
    one_spaces = AbstractVector{fpMatrix}([])

    if sub_dim == 0
        push!(collection_subspaces,zero_spaces)
    elseif sub_dim != 0
        # Create 1-spaces
        S = subspace_set(space)
        for x in S
            if x != zero_vec
                new_x = rref(x)[2]
                push!(one_spaces,new_x)
            end
        end
        one_spaces = unique(one_spaces)

        push!(collection_subspaces,zero_spaces)
        push!(collection_subspaces,one_spaces)
        if sub_dim >= 2
            for i in range(2,sub_dim)
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
    containments_fix_space(space::fpMatrix)

    Returns all spaces that contains a fixed `space` sitting in an ambient vectorspace.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function containments_fix_space(space::fpMatrix)
    field = base_ring(space)

    all_higher_spaces = []
    spaces_containing_space = AbstractVector{fpMatrix}([])
    dim = ncols(space)
    sub_dim = rank(space)

    my_space_set = subspace_set(space)

    # Push in the space it self
    push!(spaces_containing_space,space)

    # Create all higher dim spaces
    for i in range(sub_dim+1,dim)
        subs = subspaces_fix_dim(field,i,dim)
        for sub in subs
            push!(all_higher_spaces,[sub,subspace_set(sub)])
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


@doc raw"""
    containments_fix_spaceV2(space::fpMatrix)
"""
# Complety new version

function containments_fix_spaceV2(space::fpMatrix)
    dim = ncols(space)
    sub_dim = rank(space)
    field = base_ring(space)

    spaces_containing_space = AbstractVector{fpMatrix}([])
    one_spaces_space = dim_one_subs(space)
    all_ones_of_spaces = subspaces_fix_dim(field,1,dim)
    one_spaces_not_in_space = [elm for elm in all_ones_of_spaces if !(elm in one_spaces_space)]

    # Push the space itself
    push!(spaces_containing_space,space)
   
    # Push higher-dimensional spaces
    for i in range(1,dim-sub_dim)
        for combi in combinations(one_spaces_not_in_space,i)
            new_space = space
            for elm in combi
                new_space = sum_vsV2(new_space,elm)
            end
            if !(new_space in spaces_containing_space)
                push!(spaces_containing_space,new_space)
            end
        end
    end

    return spaces_containing_space
    
end
################################################################################


@doc raw"""
    matrix_collec(field::fqPolyRepField, rows::Oscar.IntegerUnion, cols::Oscar.IntegerUnion, choice=nothing::Union{Int,Nothing})

    Returns all possible non-singular matrices (identity matrix in front), with entries of the given field.

    If you put in an number for the choice, then the function will choose `choice`-many random elements for the field and return all possible matrices with those elements as entries.
"""
# Changes to old version:
# None

function  matrix_collec(field::fqPolyRepField, rows::Oscar.IntegerUnion, cols::Oscar.IntegerUnion, choice=nothing::Union{Int,Nothing})
    char = characteristic(field)
    gen = Oscar.gen(field)
    deg = Oscar.degree(field)
    MS = matrix_space(field,rows,cols)
    elements = []

    if rows==cols
        return AbstractVector{fqPolyRepMatrix}([MS(1)])
    else
        # Create the elements of the extension field
        if rows == 1
            for i in range(1,cols-rows)
                push!(elements,field(0))
                for j in range(0,char^deg-2)
                    push!(elements,gen^j)
                end
            end
        else
            for i in range(1,rows)
                push!(elements,field(0))
                for j in range(0,char^deg-2)
                    push!(elements,gen^j)
                end
            end
        end

        if  isnothing(choice)
            # Create all possible cols
            one_cols_collec = []
            helper_list = []
            for combi in combinations(elements,rows)
                push!(helper_list,combi)
            end
            helper_list = unique(helper_list)

            for i in range(1,cols-rows)
                for elm in helper_list 
                    mat = transpose(matrix(field,1,rows,elm))
                    push!(one_cols_collec,mat)
                end
            end
            
            # Create all possible >= 1 row matrices with id-mat in front
            multi_row_matrix_collec = AbstractVector{fqPolyRepMatrix}([])
            for k in combinations(one_cols_collec,cols-rows)
                A = MS(1)
                for s in range(1,cols-rows)
                    A[:,rows+s]=k[s]
                end
                push!(multi_row_matrix_collec,A)
            end
            multi_row_matrix_collec = unique(multi_row_matrix_collec)

            return multi_row_matrix_collec
        else
            elements = Random.shuffle(elements)
            
            # Create all possible cols
            one_cols_collec = []
            helper_list = []
            for combi in combinations(elements[1:choice],rows)
                push!(helper_list,combi)
            end
            helper_list = unique(helper_list)

            for i in range(1,cols-rows)
                for elm in helper_list 
                    mat = transpose(matrix(field,1,rows,elm))
                    push!(one_cols_collec,mat)
                end
            end
            
            # Create all possible >= 1 row matrices with id-mat in front 
            multi_row_matrix_collec = AbstractVector{fqPolyRepMatrix}([])
            for k in combinations(one_cols_collec,cols-rows)
                A = MS(1)
                for s in range(1,cols-rows)
                    A[:,rows+s]=k[s]
                end
                push!(multi_row_matrix_collec,A)
            end
            multi_row_matrix_collec = unique(multi_row_matrix_collec)

            return multi_row_matrix_collec
            
        end
    end
end
################################################################################


# @doc raw"""
#     gln_matrices(field::fqPolyRepField, size::Oscar.IntegerUnion)

#     Returns all gln-matrices, with entries of the given field (no extension field).
#     `Size` has to be greater equal one.
# """
# # Changes to old version:
# # There is no old version

# function gln_matrices(field::Nemo.fpField, size::Oscar.IntegerUnion)
#     char = Int(Oscar.characteristic(field))

#     # Create all possible one row matrices
#     one_rows = AbstractVector{fpMatrix}([])
#     for i in range(1,char^(size)-1)
#         array = [digits(i,base=char,pad=size)]
#         vec = matrix(field,array)
#         push!(one_rows,vec)
#     end
#     one_rows = unique(one_rows)

#     # Create all possible (size x size)-matrices
#     matrices_collec = AbstractVector{fpMatrix}([])
#     for k in multiset_permutations(one_rows,size)
#         new_mat = vcat(k)
#         if rank(new_mat) == size
#             push!(matrices_collec,new_mat)
#         end
#     end

#     return unique!(matrices_collec)
# end
################################################################################


@doc raw"""
    codim_one_subs(space::fpMatrix)

    Returns all codim. one subspaces of a fix `space`. For the zero space, it will return an empty list.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function codim_one_subs(space::fpMatrix)
    collection_of_subs = subspaces_fix_space(space)
    dim = rank(space)

    if dim != 0
        return collection_of_subs[dim]
    else
        return AbstractVector{fpMatrix}([])
    end
end
################################################################################


@doc raw"""
    dim_one_subs(space::fpMatrix)

    Returns all dim. one subspaces of a fix `space`. For the zero space, it will return an empty list and for one-space it will return the space itself.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function dim_one_subs(space::fpMatrix)
    collection_of_subs = subspaces_fix_space(space)
    dim = rank(space)

    if dim == 0
        return AbstractVector{fpMatrix}([])
    else
        return collection_of_subs[2]
    end
end
################################################################################


@doc raw"""
    diamond_list(spaces::AbstractVector{fpMatrix})

    Returns all possible diamonds of a collection of spaces living in an given ambient space.
"""
# Changes to old version:
# (1) got rid of `field`-variable
# (2) using rank instead of `subspace_dim`-func

function diamond_list(spaces::AbstractVector{fpMatrix})
    info_dict = OrderedDict([])
    diamonds = AbstractVector{AbstractVector{fpMatrix}}([])
    spaces = sort(spaces, by = x->rank(x))

    # Fill info_dict with all necesssary information: [space, dim, space containment, space_subspaces, set_subspace]
    for (id,space) in enumerate(spaces)
        all_subs = AbstractVector{fpMatrix}([])
        subs = subspaces_fix_space(space)
        for sub in subs
            for space in sub
                push!(all_subs,space)
            end
        end
        merge!(info_dict,Dict(id=>[space,rank(space),containments_fix_space(space),all_subs,subspace_set(space)]))
    end

    # Create all possible diamonds from that list
    values_list = collect(values(info_dict))
    for combi in combinations(values_list,2)
        if combi[2][2] == combi[1][2] + 2
            if issubset(combi[1][5],combi[2][5])
                inters = intersect(combi[2][4],combi[1][3])
                if issubset(inters,spaces)
                    push!(diamonds,inters)
                else
                    continue
                end
            else
                continue
            end
        elseif combi[1][2] == combi[2][2] + 2
            if issubset(combi[2][5],combi[1][5])
                inters = intersect(combi[1][4],combi[2][3])
                if issubset(inters,spaces)
                    push!(diamonds,inters)
                else
                    continue
                end
            else
                continue
            end
        else
            continue
        end
    end

    return unique!(diamonds)
end
################################################################################


@doc raw"""
    k_intervall(spaces::AbstractVector{fpMatrix})

    Returns all possible lattice k_intervalls of a collection of spaces living in an given ambient space.

    The number `k` has to be greater or equal to 2.
"""
# Changes to old version:
# (1) got rid of `field`-variable
# (2) using rank instead of `subspace_dim`-func

function k_interval(spaces::AbstractVector{fpMatrix}, k::Oscar.IntegerUnion)
    info_dict = OrderedDict([])
    diamonds = AbstractVector{AbstractVector{fpMatrix}}([])
    spaces = sort(spaces, by = x->rank(x))

    # Fill info_dict with all necesssary information: [space, dim, space containment, space_subspaces, set_subspace]
    for (id,space) in enumerate(spaces)
        all_subs = AbstractVector{fpMatrix}([])
        subs = subspaces_fix_space(space)
        for sub in subs
            for space in sub
                push!(all_subs,space)
            end
        end
        merge!(info_dict,Dict(id=>[space,rank(space),containments_fix_space(space),all_subs,subspace_set(space)]))
    end

    # Create all possible diamonds from that list
    values_list = collect(values(info_dict))
    for combi in combinations(values_list,2)
        if combi[2][2] == combi[1][2] + k
            if issubset(combi[1][5],combi[2][5])
                inters = intersect(combi[1][3],combi[2][4])
                if issubset(inters,spaces)
                    push!(diamonds,inters)
                else
                    continue
                end
            else
                continue
            end
        elseif combi[1][2] == combi[2][2] + k
            if issubset(combi[2][5],combi[1][5])
                inters = intersect(combi[2][3],combi[1][4])
                if issubset(inters,spaces)
                    push!(diamonds,inters)
                else
                    continue
                end
            else
                continue
            end
        else
            continue
        end
    end

    return unique!(diamonds)
    
end
################################################################################


@doc raw"""
    standard_projection(spaces::fpMatrix)

    Takes as input a list of subspaces of an ambient spaces and returns a list where every of these spaces is projected in one dimension lower.
    
    Here the standard projection is used, meaning we set the last coordiante for every vector of the original space to 0 and identify the space with one lower-dim space.
"""
# Changes to old version:
# there is no old version

function standard_projection(spaces::AbstractVector{fpMatrix})
    new_dim = ncols(spaces[1])-1
    projected_spaces = AbstractVector{fpMatrix}([])

    # Remove the last column of every element in `spaces` list
    for elm in spaces
        new_elm = elm[:,1:new_dim]
        if is_zero(new_elm)
            push!(projected_spaces,new_elm)
        else
            r, mat = rref(new_elm)
            push!(projected_spaces,mat[1:r,:])
        end
    end

    return unique!(projected_spaces)

end
################################################################################


@doc raw"""
    standard_embedding_higher_dim(spaces::AbstractVector{fpMatrix}, coord::Oscar-IntegerUnion)

    Takes as input a list of subspaces of an ambient spaces and returns a list where every of these spaces is embedding in the nect higher dimension.
    
    Here the standard embedding are used, meaning we add a 0 in the specified position for every vector of the original space.
"""
# Changes to old version:
# (1) got rid of `field`-variable

function standard_embedding_higher_dim(spaces::AbstractVector{fpMatrix}, coord::Oscar.IntegerUnion)
    field = base_ring(spaces[1])
    new_dim = ncols(spaces[1]) + 1
    old_dim = ncols(spaces[1])
    helper_ms = matrix_space(field,old_dim,old_dim)
    Helper_zero_mat = helper_ms(0)
    Helper_id_mat = helper_ms(1)
    zero_vec = Helper_zero_mat[:,1]

    # Create list of unit vec'S
    unit_vecs = []
    for i in range(1,old_dim)
        push!(unit_vecs,Helper_id_mat[:,i])
    end
    insert!(unit_vecs,coord,zero_vec)

    # Compute the embedding for all spaces in the list
    transformed_spaces =AbstractVector{fpMatrix}([])
    MS = matrix_space(field,old_dim,new_dim)

    for space in spaces
        zero_mat = MS(0)
        for i in range(1,new_dim)
            if i==coord
                continue
            else
                zero_mat[:,i]=unit_vecs[i]
            end
        end
        trans_mat = space*zero_mat
        push!(transformed_spaces,trans_mat)
    end

    return transformed_spaces
end


@doc raw"""
    standard_embedding_higher_dimV2(spaces::fpMatrix, coord::Oscar-IntegerUnion)
"""
# Complety new version

function standard_embedding_higher_dimV2(spaces::AbstractVector{fpMatrix}, coord::Oscar.IntegerUnion)
    field = base_ring(spaces[1])
    transformed_spaces = AbstractVector{fpMatrix}([])

    # transform all spaces in the list
    for elm in spaces
        zero_vec = transpose(matrix(field,zeros(field,1,nrows(elm))))
        push!(transformed_spaces, hcat(elm[:,1:coord-1],zero_vec,elm[:,coord:end]))
    end

    return transformed_spaces

end
################################################################################


@doc raw"""
    Möbius_func_subspace_lat(space_1::fpMatrix, space_2::fpMatrix)

    Returns the value of the Möbius-function, of the subspaces lattice, of the two fixed subspaces `space_1` and `space_2`.
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable

function Möbius_func_subspace_lat(space_1::fpMatrix, space_2::fpMatrix)
    field = base_ring(space_1)
    char = Int(characteristic(field))

    dim_sub_1 = rank(space_1)
    dim_sub_2 = rank(space_2)

    diff = dim_sub_2-dim_sub_1
    sub_contained_in = containments_fix_space(space_1)

    if space_2 in sub_contained_in
        return (-1)^(diff)*char^(binomial(diff,2))
    else
        return 0
    end
end
################################################################################


@doc raw"""
    Orthogonal_complement(space::fpMatrix)

    Returns the orthogonal complement of the `space` in a given ambient space, w.r.t. the standard dor product. 
"""
# Changes to old version:
# (1) using rank instead of `subspace_dim`-func
# (2) got rid of `field`-variable
# (3) got rid of the `matrix_space`

function orthogonal_complement(A::fpMatrix)
    field = base_ring(A)
    n = ncols(A)
    subdim = rank(A)

    one_spaces = subspaces_fix_dim(field,1,n)
    one_mat = subspaces_fix_dim(field,n,n)[1]
    zero_vec = subspaces_fix_dim(field,0,n)[1]

    if A == zero_vec
        return AbstractVector{fpMatrix}([one_mat])
    elseif A == one_mat
        return AbstractVector{fpMatrix}([zero_vec])
    else
        generators_A = []
        for i in range(1,subdim)
            push!(generators_A,A[i,:])
        end

        # Search for all one_space gen's that are not orthogonal to all gens of A 
        not_complement_elms = []
        for one_space in one_spaces
            for gen in generators_A
                if gen*transpose(one_space) != 0
                    push!(not_complement_elms,one_space)
                else
                    continue
                end
            end
        end

        # Get one-spaces that are not in not_complement_elms
        complement_elms = []
        for one_space in one_spaces
            if !(one_space in not_complement_elms)
                push!(complement_elms,one_space)
            end
        end

        # Construct a matrix out of this vectors
        orth_comp_as_matrix = AbstractVector{fpMatrix}([]) 
        for i in combinations(complement_elms,n-subdim)
            r,matrix = rref(vcat(i))
            if r == n-subdim
                push!(orth_comp_as_matrix,matrix)
            end
        end
        orth_comp_as_matrix = unique(orth_comp_as_matrix)


        return orth_comp_as_matrix
    end
end


@doc raw"""
    Orthogonal_complementV2(space::fpMatrix)
"""
# Completely new version 

function orthogonal_complementV2(A::fpMatrix)
    r, rref_ker_A = rref(transpose(right_kernel(A)[2]))

    return [rref_ker_A[1:r,:]]
end
################################################################################



################################################################################
# Encoding/Decoding section
################################################################################


@doc raw"""
    binary_encoding(k_spaces::AbstractVector{fpMatrix}, all_k_spaces::AbstractVector{fpMatrix})

    Returns one 1-0-Array of length #`all_k_spaces` as the binary-encoding of the given `k_spaces`-list.
    Here we set a 1 for a space in `all_k_spaces` if this space is also in `k_spaces` and 0 else.
    The ordering of the Array is induced by the ordering of the `all_k_spaces`-list, which is the ordering coming from the `subspaces_fix_dim` function.
    If `no_dict==false` then the fcuntion will return a dictionary with entries: [1 or 0,space].
"""
# Changes to old version:
# there is no old version

function binary_encoding(k_spaces::AbstractVector{fpMatrix}, all_k_spaces::AbstractVector{fpMatrix},no_dict=true)
    encoded_dict = OrderedDict([])
    # Iterate through the `all_k_spaces`-list: add a one if the current element is in `k_spaces` and a zero else
    for (id,elm) in enumerate(all_k_spaces)
        if elm in k_spaces
            merge!(encoded_dict,Dict(id=>[1,elm]))
        else
            merge!(encoded_dict,Dict(id=>[0,elm]))
        end
    end

    if no_dict
        encoded_array = [elm[1] for elm in collect(values(encoded_dict))]
        return encoded_array
    elseif no_dict==false
        return encoded_dict
    end

end
################################################################################


@doc raw"""
    sub_encoding(spaces::AbstractVector{fpMatrix}, ones_dict::OrderedDict, char=false::Bool)

    Returns a list of the encodings of the elements in `spaces`.
    The encoding of a subspace is a list of the 1-spaces it contains.
    If you set the `char`-value to `true`, the function will additionally return the field-characteristic.. 
"""
# Changes to old version:
# there is no old version

function sub_encoding(spaces::AbstractVector{fpMatrix}, ones_dict::OrderedDict, char=false::Bool)

    # Encode every element in the `spaces`-list
    endcoded_list = AbstractVector{AbstractVector{Int}}([])
    for elm in spaces
        one_subs = dim_one_subs(elm)
        elm_ones_list = AbstractVector{Int}([0])
        for (k,v) in ones_dict
            if v in one_subs
                push!(elm_ones_list,k)
            end
        end
        push!(endcoded_list,elm_ones_list)
    end

    if endcoded_list == [[]]
        if char == true
            q = Int(characteristic(base_ring(ones_dict[1])))
            return AbstractVector{AbstractVector{Int}}([[0]]), q
        else
            return AbstractVector{AbstractVector{Int}}([[0]])
        end
    else
        if char == true
            q = Int(characteristic(base_ring(ones_dict[1])))
            return endcoded_list, q
        else
            return endcoded_list
        end
    end

end


@doc raw"""
    sub_decoding(endcoded_list::AbstractVector{AbstractVector{Int}}, ones_dict::OrderedDict)

    Returns a list of the decodings, so the actual spaces, of the elements in the `encoded_list`.
    The encoding of a subspace is a list of the 1-spaces it contains.
"""
# Changes to old version:
# there is no old version

function sub_decoding(encoded_list::AbstractVector{AbstractVector{Int}}, ones_dict::OrderedDict)
    # Decode every element in the `encoded_list`-list
    decoded_list = AbstractVector{fpMatrix}([])
    for elm in encoded_list
        value_list = [ones_dict[num] for num in elm if num != 0]
        if isempty(value_list)
            field = base_ring(ones_dict[1])
            zero_vec = matrix(field,zeros(field,1,ncols(ones_dict[1])))
            insert!(decoded_list,1,zero_vec)
        else
            r,rref_mat = rref(vcat(value_list))
            push!(decoded_list,rref_mat[1:r,:])
        end
    end

    return decoded_list
    

end
################################################################################


@doc raw"""
    encoded_containments_fix_space(endcoded_space::AbstractVector{Int}, encoded_all_spaces::AbstractVector{AbstractVector{Int}})

    Returns the encoding of all spaces containing the given `endcoded_space`.
"""
# Changes to old version:
# there is no old version

function encoded_containments_fix_space(encoded_space::AbstractVector{Int}, encoded_all_spaces::AbstractVector{AbstractVector{Int}})
    # Check issubset of `encoded_space` in every elm from `encoded_all_spaces`
    len_encoded_space = length(encoded_space)
    encoded_superspaces = AbstractVector{AbstractVector{Int}}([])

    for elm in encoded_all_spaces
        if length(elm) >= len_encoded_space && issubset(encoded_space,elm)
            push!(encoded_superspaces,elm)
        end
    end

    return encoded_superspaces

end
################################################################################


@doc raw"""
    encoded_subspaces_fix_space(encoded_space::AbstractVector{Int}, encoded_all_spaces::AbstractVector{AbstractVector{Int}})

    Returns the encoding of all spaces contained in the given `endcoded_space`.
"""
# Changes to old version:
# there is no old version

function encoded_subspaces_fix_space(encoded_space::AbstractVector{Int}, encoded_all_spaces::AbstractVector{AbstractVector{Int}})
    # Check issubset of every elm from `encoded_all_spaces` in `encoded_space`
    len_encoded_space = length(encoded_space)
    encoded_subspaces = AbstractVector{AbstractVector{Int}}([])

    for elm in encoded_all_spaces
        if length(elm) <= len_encoded_space && issubset(elm,encoded_space)
            push!(encoded_subspaces,elm)
        end
    end

    return encoded_subspaces

end
################################################################################


@doc raw"""
    encoded_k_interval(encoded_spaces::AbstractVector{Int}, char::Oscar.IntegerUnion, k::Oscar.IntegerUnion, encoded_all_spaces::AbstractVector{AbstractVector{Int}})

    Returns all possible lattice k_intervalls of a collection of `encoded_spaces` living in an given encoded ambient space.

    The number `k` has to be greater or equal to 2.
"""
# Changes to old version:
# there is no old version

function encoded_k_interval(encoded_spaces::AbstractVector{AbstractVector{Int}}, char::Oscar.IntegerUnion, k::Oscar.IntegerUnion, encoded_all_spaces::AbstractVector{AbstractVector{Int}})
    info_dict = OrderedDict([])
    k_intervalls = AbstractVector{AbstractVector{AbstractVector{Int}}}([])
    encoded_spaces = sort(encoded_spaces, by = x->length(x))


    # Fill info_dict with all necesssary information: [en_space, dim, en_space containments, en_space subspaces]
    for (id,elm) in enumerate(encoded_spaces)
        a = length(elm)-1
        dim = Int(log(char,a*(char-1)+1))
        merge!(info_dict,Dict(id=>[elm,dim,encoded_containments_fix_space(elm,encoded_all_spaces),encoded_subspaces_fix_space(elm,encoded_all_spaces)]))
    end

    # Create all possible k-intervalls from the `encoded_spaces`-list
    keys_infod = collect(keys(info_dict))
    for combi in combinations(keys_infod,2)
        if info_dict[combi[2]][2] == info_dict[combi[1]][2] + k
            if issubset(info_dict[combi[1]][1],info_dict[combi[2]][1])
                inters = intersect(info_dict[combi[1]][3],info_dict[combi[2]][4])
                if issubset(inters,encoded_spaces)
                    push!(k_intervalls,inters)
                end
            end
        elseif info_dict[combi[1]][2] == info_dict[combi[2]][2] + k
            if issubset(info_dict[combi[2]][1],info_dict[combi[1]][1])
                inters = intersect(info_dict[combi[2]][3],info_dict[combi[1]][4])
                if issubset(inters,encoded_spaces)
                    push!(k_intervalls,inters)
                end
            end
        end
    end

    return unique!(k_intervalls)

end
################################################################################