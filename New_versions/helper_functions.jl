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
    field = base_ring(space_1)
    zero_mat = matrix_space(field,ncols(space_1),ncols(space_1))(0)
    zero_vec = zero_mat[1,:]

    New_mat = vcat(space_1,space_2)
    r,rref_mat = rref(New_mat)

    if rref_mat == zero_mat
        return zero_vec
    else
        return rref_mat[1:r,:]
    end
end
################################################################################


@doc raw"""
    inters_vs(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)

    Returns the vs-intersection of the two subspaces `space_1` `space_2` sitting in an ambient vectorspace.
"""
function inters_vs(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)
    dim = ncols(space_1)
    ms = matrix_space(field,1,dim)
    zero_vec = ms(0)

    subs_1 = subspaces_fix_space(field,space_1)
    subs_2 = subspaces_fix_space(field,space_2)

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

    # Cumpute intersecton of subs_list_1, subs_list_2
    inters_list = intersect(subs_list_1,subs_list_2)

    # Choose the element with maximal dim in that List
    inters = AbstractVector{fpMatrix}([y for y in inters_list[findall(x->subspace_dim(field,x)==maximum(z->subspace_dim(field,z),inters_list),inters_list)]])

    return inters
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


@doc raw"""
    matrix_collec(field::fqPolyRepField, rows::Oscar.IntegerUnion, cols::Oscar.IntegerUnion, choice=nothing::Union{Int,Nothing})

    Returns all possible non-singular matrices (identity matrix in front), with entries of the given field.

    If you put in an number for the choice, then the function will choose `choice`-many random elements for the field and return all possible matrices with those elements as entries.
"""
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
# (2) got rid of `field`-variable#

function  dim_one_subs(space::fpMatrix)
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
    diamond_list(field::Nemo.fpField, spaces::AbstractVector{fpMatrix})

    Returns all possible diamonds of a collection of spaces living in an given ambient space.
"""
function diamond_list(field::Nemo.fpField, spaces::AbstractVector{fpMatrix})
    info_dict = OrderedDict([])
    diamonds = AbstractVector{AbstractVector{fpMatrix}}([])
    spaces = sort(spaces, by = x->subspace_dim(field,x))

    # Fill info_dict with all necesssary information: [space, dim, space containment, space_subspaces, set_subspace]
    for (id,space) in enumerate(spaces)
        all_subs = AbstractVector{fpMatrix}([])
        subs = subspaces_fix_space(field,space)
        for sub in subs
            for space in sub
                push!(all_subs,space)
            end
        end
        merge!(info_dict,Dict(id=>[space,subspace_dim(field,space),containments_fix_space(field,space),all_subs,subspace_set(field,space)]))
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
    k_intervall(field::Nemo.fpField, spaces::AbstractVector{fpMatrix})

    Returns all possible lattice k_intervalls of a collection of spaces living in an given ambient space.

    The number `k` has to be greater or equal to 2.
"""
function k_interval(field::Nemo.fpField, spaces::AbstractVector{fpMatrix}, k::Oscar.IntegerUnion)
    info_dict = OrderedDict([])
    diamonds = AbstractVector{AbstractVector{fpMatrix}}([])
    spaces = sort(spaces, by = x->subspace_dim(field,x))

    # Fill info_dict with all necesssary information: [space, dim, space containment, space_subspaces, set_subspace]
    for (id,space) in enumerate(spaces)
        all_subs = AbstractVector{fpMatrix}([])
        subs = subspaces_fix_space(field,space)
        for sub in subs
            for space in sub
                push!(all_subs,space)
            end
        end
        merge!(info_dict,Dict(id=>[space,subspace_dim(field,space),containments_fix_space(field,space),all_subs,subspace_set(field,space)]))
    end

    # Create all possible diamonds from that list
    values_list = collect(values(info_dict))
    for combi in combinations(values_list,2)
        if combi[2][2] == combi[1][2] + k
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
        elseif combi[1][2] == combi[2][2] + k
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
    standard_embedding_higher_dim(field::Nemo.fpField, space::fpMatrix, coord::Oscar-IntegerUnion)

    Takes as input a list of subspaces of an ambient spaces and returns a list where every of these spaces is embedding in the nect higher dimension.
    
    Here the standard embedding are used, meaning we add a 0 in the specified position for every vector of the original space.
"""
function standard_embedding_higher_dim(field::Nemo.fpField, spaces::AbstractVector{fpMatrix}, coord::Oscar.IntegerUnion)
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
################################################################################


@doc raw"""
    Möbius_func_subspace_lat(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)

    Returns the value of the Möbius-function, of the subspaces lattice, of the two fixed subspaces `space_1` and `space_2`.
"""
function Möbius_func_subspace_lat(field::Nemo.fpField, space_1::fpMatrix, space_2::fpMatrix)

    char = Int(characteristic(field))

    dim_sub_1 = subspace_dim(field,space_1)
    dim_sub_2 = subspace_dim(field,space_2)

    diff = dim_sub_2-dim_sub_1
    sub_contained_in = containments_fix_space(field,space_1)

    if space_2 in sub_contained_in
        return (-1)^(diff)*char^(binomial(diff,2))
    else
        return 0
    end
end
################################################################################


@doc raw"""
    Orthogonal_complement(field::Nemo.fpField, space::fpMatrix)

    Returns the orthogonal complement of the `space` in a given ambient space, w.r.t. the standard dor product. 
"""
function orthogonal_complement(field::Nemo.fpField, A::fpMatrix)
    n = ncols(A)
    subdim = subspace_dim(field,A)
    one_spaces = subspaces_fix_dim(field,1,n)
    MS = matrix_space(field,n,n)
    one_mat = MS(1)
    zero_vec = MS(0)[1,:]

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
################################################################################