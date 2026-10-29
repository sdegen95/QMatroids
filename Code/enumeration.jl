################################################################################
##  Enumeration using linear subclass selectors
################################################################################
include("helper_functions.jl")
include("q_matroids.jl")
include("q_properties.jl")

GAP.Packages.load("images")  # once per session

###########################################################################################
# !!!Any matrix you input in a function/method needs to be in RREF!!!
###########################################################################################


################################################################################
## Helper function for the deep first search algo
################################################################################

@doc raw"""
    Lex_compare_subs(sub1:: Any, sub2::Any)

    Compares the two subspaces `sub1` and `sub2` w.r.t. to the linear order defined in Chapter 6, Section 4.1., of my thesis.
    It assumes in the beginning that `sub1`<`sub2` and returns `true` if it is and `false` if `sub1`>`sub2`. 
    Note that the subspaces need to have the same dimension!!!

    !!!Important: Currently this function only works for GF(2)!!!
"""
function Lex_compare_subs(sub1:: Any, sub2::Any)
    # Lift subspaces
    # sub1t = lift.(sub1)
    # sub2t = lift.(sub2)
    sub1t = map(x -> iszero(x) ? 0 : 1, sub1)
    sub2t = map(x -> iszero(x) ? 0 : 1, sub2) # This part only work in GF(2) for now, but can be easily adapted to other fields
    sub1_smaller_sub2 = true
    r = rank(sub1)
    dim = ncols(sub1)

    if iszero(sub1t[:,dim]) == true && iszero(sub2t[:,dim]) == false
        return sub1_smaller_sub2
    elseif iszero(sub1t[:,dim]) == false && iszero(sub2t[:,dim]) == true
        sub1_smaller_sub2 = false
        return sub1_smaller_sub2
    elseif iszero(sub1t[:,dim]) == true && iszero(sub2t[:,dim]) == true
        # Count number of zero columns
        count_1 = 0
        count_2 = 0
        for i in range(1,dim-r)
            if iszero(sub1t[:,r+i]) == true && iszero(sub1t[:,r+i:dim])==true 
                count_1 += 1
            end
            if iszero(sub2t[:,r+i]) == true && iszero(sub2t[:,r+i:dim])==true
                count_2 += 1
            end
        end
        #println("count_1 = $count_1, count_2 = $count_2")

        if count_1 > count_2
            return sub1_smaller_sub2
        elseif count_1 < count_2
            sub1_smaller_sub2 = false
            return sub1_smaller_sub2
        elseif count_1 == count_2
            for i in range(1,r)
                row1i = sub1t[i,:]
                row2i = sub2t[i,:]
                diff_vec = row1i-row2i
                
                if iszero(diff_vec) == false
                    #println("here")
                    firstpos = findfirst(x -> x != 0, diff_vec)
                    
                    if diff_vec[firstpos] < 0
                        break
                        
                    elseif diff_vec[firstpos] > 0
                        sub1_smaller_sub2 = false
                        break

                    end
                end
                
            end

            return sub1_smaller_sub2
        end
    elseif iszero(sub1t[:,dim]) == false && iszero(sub2t[:,dim]) == false
        for i in range(1,r)
            row1i = sub1t[i,:]
            row2i = sub2t[i,:]
            diff_vec = row1i-row2i
            
            if iszero(diff_vec) == false
                #println("here")
                firstpos = findfirst(x -> x != 0, diff_vec)
                
                if diff_vec[firstpos] < 0
                    break
                    
                elseif diff_vec[firstpos] > 0
                    sub1_smaller_sub2 = false
                    break

                end
            end
            
        end
        
        return sub1_smaller_sub2

    end

end
################################################################################

@doc raw"""
    Q_Matroid_linear-subclasses(QM::Q_Matroid, hyps::Any))

    This returns the collection of all linear subclasses of the given q-matroid.
"""

function Q_Matroid_linear_subclasses(QM::Q_Matroid, hyps::Any)

    # Compute the corank 2 flats of the q-matroid
    corank2 = Q_Matroid_Corank2Flats(QM)

    # Compute all the super-hyperplanes of the corank 2 flats
    super_sp_dict = OrderedDict([flat => containments_fix_spaceV2(flat) for flat in corank2])

    # Create a dictonary for the hyperplanes
    #hyp_dict = OrderedDict([id => hyp for (id, hyp) in enumerate(hyps)])

    # 
    lqs_col = AbstractVector{Any}([[],hyps])
    lqs_col_sets = [Set([]),Set(hyps)]
    iter_bound = length(hyps)

    # Iterate over all possible initial hyperplane choices
    for i in range(1,iter_bound)

        # Define stack shape
        stack = [] # stack_elements: [lqs, remaining_hyps,seen_inters_pairs]

        # Compute Initial node
        init_lqs = AbstractVector{Any}([hyps[i]])
        push!(lqs_col,init_lqs)
        push!(lqs_col_sets,Set(init_lqs))
        init_remaining = setdiff(hyps,init_lqs)
        init_node = [init_lqs, init_remaining,[]]

        # Now push the `Init_node` into the stack
        push!(stack,init_node)

        # DFS-Algo
        while length(stack)!=0
            current_node = pop!(stack)

            if length(current_node[2]) != 0

                for h in current_node[2]
                    new_lqs = push!(copy(current_node[1]),h)
                    new_seen_inters_pairs = copy(current_node[3])
                    for combi in Oscar.combinations(new_lqs,2)
                        if !(Set(combi) in current_node[3])
                            push!(new_seen_inters_pairs,Set(combi))
                            inters = inters_vsV3(combi[1],combi[2])
                            if inters in corank2
                                inters_super_hyps = intersect(super_sp_dict[inters], hyps)
                                for s in inters_super_hyps
                                    if !(s in new_lqs)
                                        push!(new_lqs,s)
                                    end
                                end
                            end
                        end
                    end
                    new_remaining = setdiff(copy(current_node[2]),new_lqs)
                    push!(stack,[new_lqs, new_remaining,new_seen_inters_pairs])

                    if !(Set(new_lqs) in lqs_col_sets)
                        push!(lqs_col_sets,Set(new_lqs))
                        push!(lqs_col,new_lqs)
                    end
                end

            # else
            #     push!(lqs_col,current_node[1])
            end
        end
        

        # Progress
        println("$i. choice of $iter_bound done")
        println("-------------------------------------")

        # Empty stack
        empty!(stack)
    end

    return unique!(lqs_col)
end
################################################################################

@doc raw"""
    Initial_linear_subclasses(hyps::Any, lqs_collection::Any, dim::Any, field::Any,stab=false::Any)

    This returns the collection of all linear subclasses that are need for an initial input in the below algo.
"""

function Initial_linear_subclasses(hyps::Any, lqs_collection::Any, dim::Any, field::Any, stab=false::Any) 

    # Compute automorphism group of QM
    GLn = Oscar.general_linear_group(dim, field)
    hyps_set = Set(hyps)

    actfn = function(spaces,G)
        return Set([rref(C*transpose(matrix(G)))[2] for C in spaces])
    end

    #S, emb = stabilizer(GLn, hyps_set, actfn)
    S = [g for g in GLn if actfn(Set(hyps),g)==Set(hyps)]

    # Compute the orbits of the lqs under the action of S
    # Appearing lqs in some orbit get removed from the lqs_collection

    init_lqs_collection = []
    seen_list = []
    for l in lqs_collection
        if !(Set(l) in seen_list)
            push!(init_lqs_collection,l)
            for s in S
                act_l = actfn(Set(l),s)
                push!(seen_list,act_l)
            end
        end
    end
    
    if stab == true
        return  init_lqs_collection, S
    else
        return init_lqs_collection
    end
    
end
################################################################################

@doc raw"""
    Initial_linear_subclassesV2(hyps::Any, lqs_collection::Any, dim::Any, field::Any, stab=false::Any)

    This returns the collection of all linear subclasses that are need for an initial input in the below algo.
"""
# Faster version.

function Initial_linear_subclassesV2(hyps::Any, lqs_collection::Any, dim::Any, field::Any, stab=false::Any) 

    # Compute automorphism group of QM
    GLn = Oscar.general_linear_group(dim, field)
    hyps_set = Set(hyps)

    actfn = function(spaces,G)
        return Set([rref(C*matrix(G))[2] for C in spaces])
    end

    S, emb = stabilizer(GLn, hyps_set, actfn)
    #S = [g for g in GLn if actfn(Set(hyps),g)==Set(hyps)]

    # Compute the orbits of the lqs under the action of S
    # Appearing lqs in some orbit get removed from the lqs_collection

    init_lqs_collection = []
    seen_list = []
    for l in lqs_collection
        if !(Set(l) in seen_list)
            push!(init_lqs_collection,l)
            for s in S
                act_l = actfn(Set(l),s)
                push!(seen_list,act_l)
            end
        end
    end
    
    if stab == true
        return  init_lqs_collection, S
    else
        return init_lqs_collection
    end
    
end
################################################################################

@doc raw"""
    LS_selector_to_bases(lqs_selector:: Any, ones_dict:: Any, indeps::Any, emb_bases::Any, qrankm1_subs:: Any)

    Returns the bases of the single-extension q-matroid associated to the given linear subclass selector.    
"""

function LS_selector_to_bases(lqs_selector:: Any, ones_dict:: Any, indeps::Any, emb_bases::Any, qrankm1_subs:: Any)
    ext_bases = [x for x in emb_bases]
    
    for elm in lqs_selector
        all_subs = []
        for h in elm[2]
            subs = reduce(vcat,subspaces_fix_space(h))
            #println(subs)
            inters = intersect(subs,qrankm1_subs)
            union!(all_subs,inters)
            #= for x in inters
                push!(all_subs,x)
            end =#
        end
        #println(all_subs)

        for x in indeps
            #println(!(x[1] in all_subs))
            if !(x[1] in all_subs)
                sum = sum_vsV2(x[2],ones_dict[elm[1]])
                push!(ext_bases,sum)
            end
        end
    end

    return unique!(ext_bases)

end
################################################################################

###########################################################################################
## Canonical forms
###########################################################################################

@doc raw"""
    Mats_to_PermsV2(Mats::Any, space_dict::Any)

    Encodes a list of matrices into a list of permutations of k-spaces for some 1<k<ambient dimension.
"""

function Mats_to_PermsV2(Mats::Any, space_dict::Any)
    S = symmetric_group(length(space_dict))
    permlist = []
    
    for M in Mats
        M_array = [rref(x*matrix(M))[2] for x in keys(space_dict)]
        M_perm = [space_dict[x] for x in M_array]
        push!(permlist, M_perm)
    end
    gens = [S(p) for p in permlist]
    
    return Oscar.sub(S, gens)[1]
end

@doc raw"""
    Canonical_context(field::Any, k::Any, dim::Any)

    Pre-computes what is needed to canonicalize rank-`k` q-matroids on `field^dim`: the
    k-subspaces in order, their index dictionary, and the image of GL(dim,field) as a
    permutation group on them.
"""

function Canonical_context(field::Any, k::Any, dim::Any)
    qrank_subs = subspaces_fix_dim(field, k, dim)
    sort!(qrank_subs; lt = Lex_compare_subs)
    space_dict = OrderedDict([x => id for (id,x) in enumerate(qrank_subs)])

    GLn = Oscar.general_linear_group(dim, field)
    GL_perm = Mats_to_PermsV2(gens(GLn), space_dict)

    return (qrank_subs = qrank_subs,
            space_dict = space_dict,
            GL_perm    = GL_perm,
            K          = length(qrank_subs))
end
################################################################################

@doc raw"""
    Minimal_image_perm(G::PermGroup, S::Vector{Int})

    Lexicographically smallest image of the set `S` under `G`, via the GAP package "images".
"""

function Minimal_image_perm(G::PermGroup, S::Vector{Int})
    if length(S) == 0
        return Int[]
    end
    gS = GapObj(sort!(copy(S)); recursive=true)
    m = GAP.Globals.MinimalImage(GapObj(G), gS, GAP.Globals.OnSets)

    return Vector{Int}(m)
end
################################################################################

@doc raw"""
    Base_indices(bases::Any, ctx::Any)

    Positions of the `bases` among all k-subspaces, i.e., the support of the encoding in Chapter 6, Section 4.1., of my thesis.
"""

function Base_indices(bases::Any, ctx::Any)
    return sort([ctx.space_dict[B] for B in bases])
end
################################################################################

@doc raw"""
    Canonical_indices(indices::Vector{Int}, ctx::Any)
    Canonical_indices(bases::Any, ctx::Any)

    Support of the smallest encoding in the isomorphism class, i.e., the canonical
    representative given by its positions. Takes either the positions of
    the bases, as `Base_indices` returns them, or the bases themselves.
"""

function Canonical_indices(indices::Vector{Int}, ctx::Any)
    complement = setdiff(1:ctx.K, indices)

    return setdiff(1:ctx.K, Minimal_image_perm(ctx.GL_perm, complement))
end

function Canonical_indices(bases::Any, ctx::Any)
    return Canonical_indices(Base_indices(bases,ctx), ctx)
end
################################################################################

@doc raw"""
    Is_canonical_q_matroid(bases::Any, ctx::Any)

    Tests if the encoding of the given q-matroid is canonical, i.e., the smallest one in its whole
    isomorphism class.
"""

function Is_canonical_q_matroid(bases::Any, ctx::Any)
    return Base_indices(bases,ctx) == Canonical_indices(bases,ctx)
end
################################################################################

@doc raw"""
    Canonical_q_matroid_fast(bases::Any, ctx::Any)

    Returns the bases of the canonical representative of the isomorphism class of the given q-matroid.
"""

function Canonical_q_matroid_fast(bases::Any, ctx::Any)
    return AbstractVector{Any}([ctx.qrank_subs[i] for i in Canonical_indices(bases,ctx)])
end
################################################################################

###########################################################################################
# The trivial extensions, i.e. the second loop of Algorithm C
###########################################################################################

@doc raw"""
    Trivial_extension(QM::Q_Matroid)

    Trivial extension of a rank-`k` q-matroid on `field^n` to a rank-`(k+1)` q-matroid on
    `field^(n+1)`, the one induced by the trivial modular cut selector.
"""

function Trivial_extension(QM::Q_Matroid)
    dim = ncols(QM.groundspace) + 1
    field = base_ring(QM.groundspace)
    id_mat = matrix_space(field,dim,dim)(1)

    emb_bases = standard_embedding_higher_dimV2(QM.bases, dim)
    new_ones = [x for x in subspaces_fix_dim(field,1,dim) if !iszero(x[dim])]

    ext_bases = Set()
    for B in emb_bases
        for v in new_ones
            push!(ext_bases, rref(vcat(B,v))[2])
        end
    end

    return Q_Matroid(id_mat, AbstractVector{Any}([x for x in ext_bases]))
end
################################################################################

@doc raw"""
    Rank_one_q_matroids(field::Any, n::Any)

    Return the the `n` non-isomorphic q-matroids of rank 1 on `field^n`.

    Up to isomorphism such a q-matroid is determined by the dimension of its space of loops,
    which runs through 0,...,n-1, and its bases are the one-spaces outside that space.
"""

function Rank_one_q_matroids(field::Any, n::Any)
    id_mat = matrix_space(field,n,n)(1)
    ones = subspaces_fix_dim(field,1,n)
    q_matroids = []

    for loop_dim in range(0,n-1)
        # the space of loops is spanned by the first `loop_dim` unit vectors
        bases = [x for x in ones if !iszero(x[:,loop_dim+1:n])]
        push!(q_matroids, Q_Matroid(id_mat, AbstractVector{Any}(bases)))
    end

    return q_matroids
end
################################################################################

################################################################################
## Depth-first search 
################################################################################

@doc raw"""
    Hyperplane_induced_partition(space::Any, ones_dict::Any)

    This inputs a `space` H and a non-empty dictionary of one-spaces `ones_dict`.
    It outputs a partition p_H=(B_1,...,B_n) of the one-spaces w.r.t. to the rule: e_i,e_j in B_n if H+e_i = H+e_j.  
"""
function Hyperplane_induced_partition(space::Any, ones_dict::Any)
    partition = []
    seen_list = AbstractVector{Any}([])
    ones = values(ones_dict)

    # Get the partition in terms of one-spaces
    for e in ones
        if !(e in seen_list)
            sum = sum_vsV2(space,e)
            ones_sum = intersect(dim_one_subs(sum),ones)
            block = AbstractVector{Any}([])
            for x in ones_sum
                push!(seen_list,x)
                push!(block,x)
            end
            push!(partition,block)
        end
    end

    # Transform the above partition into a partition using the dict indices
    new_partition = []
    indices = keys(ones_dict)

    for b in partition
        new_b = []
        for x in b
            ind_x = [ind for ind in indices if ones_dict[ind] == x]
            new_b = vcat(new_b,ind_x)
        end
        push!(new_partition,sort(new_b))
    end

    return new_partition
end
################################################################################

@doc raw"""
    DFS_restrictions_dict(ind:: Any, lqs:: Any, hyp_partition_dict:: Any, max_depth:: Any)

    ....
"""

function DFS_restrictions_dict(ind:: Any, lqs:: Any, hyp_partition_dict:: Any, max_depth:: Any)
    restrictions_list = [[num,[],[]] for num in range(1,max_depth)]

    # Compute restriction for the other indicies bases on the current one `ind`
    for key in keys(hyp_partition_dict)
        partition = hyp_partition_dict[key]
        ind_block = partition[findall(x -> issubset(ind,x), partition)[1]]
        #println(ind_block)
        if key in lqs
            for x in ind_block
                if !(x in range(1,ind))
                    for elm in restrictions_list
                        if elm[1]==x 
                            push!(elm[2],key)
                        end
                    end
                end
            end
        else
            for x in ind_block
                if !(x in range(1,ind))
                    for elm in restrictions_list
                        if elm[1]==x 
                            push!(elm[3],key)
                        end
                    end
                end
            end
        end
    end

    # Transform list into dictionary for better accessability 
    restrictions_dict = OrderedDict([elm[1] => [elm[2],elm[3]] for elm in restrictions_list])

    return restrictions_dict
end
################################################################################

@doc raw"""
    DFS_possible_options(ind:: Any, lqs_collection:: Any, restrictions_dict:: Any)

    ....
"""

function DFS_possible_options(ind:: Any, lqs_collection:: Any, restrictions_dict:: Any)
    lqs_options = []
    restrictions_pos = restrictions_dict[ind][1]
    restrictions_neg = restrictions_dict[ind][2]

    for elm in lqs_collection
        if issubset(restrictions_pos,elm) && length(intersect(restrictions_neg,elm))==0
            push!(lqs_options,elm)
        end
    end

    return lqs_options
end
################################################################################

@doc raw"""
    DFS_collect(stack::Any, hyp_partition_dict::Any, lqs_collection::Any, max_depth::Any,
                        result_list::Any, ones_dict::Any, qrankm1_subs::Any, emb_bases::Any, indeps::Any)

    ....
"""

function DFS_collect(stack:: Any, hyp_partition_dict:: Any, lqs_collection:: Any, max_depth:: Any,
                             result_list::Any, ones_dict::Any, qrankm1_subs:: Any, emb_bases:: Any, indeps::Any)

    while length(stack)!=0
        current_node = pop!(stack)

        if current_node[1] < max_depth

            # Raise the current_index
            new_current_index = current_node[1]+1

            # Calculate the options of the current node
            options = DFS_possible_options(new_current_index,lqs_collection,current_node[3])

            # Compute restrictions_dicts of all the options and insert all options_nodes of the current node before the node in the stack
            if length(options) != 0
                if new_current_index == max_depth
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        options_node = [new_current_index, new_lqs_selector,"no restriction_dict"]
                        push!(stack,options_node)
                    end
                else
                    for option in options
                        new_lqs_selector = copy(current_node[2])
                        push!(new_lqs_selector, [new_current_index, option])
                        rest_dict_option = DFS_restrictions_dict(new_current_index,option,hyp_partition_dict,max_depth)
                        new_restrictions_dict = OrderedDict([id=>[vcat(current_node[3][id][1],rest_dict_option[id][1]),
                                                                vcat(current_node[3][id][2],rest_dict_option[id][2])] for id in range(new_current_index+1,max_depth)])
                        options_node = [new_current_index,new_lqs_selector,new_restrictions_dict]
                        push!(stack,options_node)
                    end
                end
            end

        elseif current_node[1] == max_depth

            # Check the linear-q-subclass selector condition for the current node
            holds = true
            for combi in Oscar.combinations(current_node[2],2)
                loop = true
                inters = intersect(combi[1][2],combi[2][2])
                if  length(inters) != 0
                    u = [combi[1][1],combi[2][1]]
                    for h in inters
                        counter = 0
                        part = hyp_partition_dict[h]
                        for b in part
                            if issubset(u,b)
                                counter += 1
                            end
                        end
                        if counter == 0
                            loop = false
                            break
                        end
                    end
                end
                if loop == false
                    holds = false
                    break
                end
            end

            if holds
                push!(result_list, [current_node[2], LS_selector_to_bases(current_node[2],ones_dict,indeps,emb_bases,qrankm1_subs)])
            end
        end
    end
end
################################################################################

@doc raw"""
    DFS_enum_collect(QM::Q_Matroid, info=false::Any)

    Generates all possible linear subclass selectors of the given q-matroid.
    Returns the asscociated single-extension q-matroids.

    `info=true` additionally also returns the hyperplanes and the one-spaces corresponding to the inputted q-matroid. 
"""

function DFS_enum_collect(QM:: Q_Matroid, info=false:: Any)
    dim = ncols(QM.groundspace)+1
    field = base_ring(QM.groundspace)
    result_list = []

    # Compute the bases, (rank-1)-dim. independent spaces and embed them
    O_bases = QM.bases
    q_rank = rank(O_bases[1])
    qrankm1_subs = subspaces_fix_dim(field,q_rank-1,dim-1)
    O_indeps = intersect(Q_Matroid_Independentspaces(QM),qrankm1_subs)
    emb_bases = standard_embedding_higher_dimV2(O_bases,dim)
    indeps = [[I,standard_embedding_higher_dimV2([I],dim)[1]] for I in O_indeps]

    # Compute the new appearing one-spaces in dim+1
    ones = [x for x in subspaces_fix_dim(field,1,dim) if x[dim]!=0]
    ones_dict = OrderedDict([id => x for (id,x) in enumerate(ones)])
    max_depth = length(ones)

    # Compute all induced hyperplane partitions
    hyps = Q_Matroid_Hyperplanes(QM)
    hyp_partition_dict = OrderedDict([h => Hyperplane_induced_partition(standard_embedding_higher_dimV2([h],dim)[1],ones_dict) for h in hyps])

    # Compute all lqs
    lqs_collection = Q_Matroid_linear_subclasses(QM, hyps)
    init_collection = Initial_linear_subclassesV2(hyps,lqs_collection,dim-1,field)

    # Iterate over all possible initial lqs choices
    for i in range(1,length(init_collection))
        current_index = 1
        stack = []

        lqs = init_collection[i]
        lqs_selector = [[current_index, lqs]]
        restrictions_dict = DFS_restrictions_dict(current_index,lqs,hyp_partition_dict,max_depth)
        push!(stack,[current_index,lqs_selector,restrictions_dict])

        DFS_collect(stack, hyp_partition_dict, lqs_collection, max_depth, result_list,
                            ones_dict, qrankm1_subs, emb_bases, indeps)
        empty!(stack)
    end

    if info
        return unique!(result_list), hyps, ones_dict
    else
        return unique!(result_list)
    end
end
################################################################################

###########################################################################################
# Algorithm
###########################################################################################

@doc raw"""
    start_enum_canonical(qm_list::Any, qm_list_lower=[]::Any, info=true::Any, collect_leaves=true::Any)

    Algorithm C in Chapter 6, Section 4.3., of my thesis.
    Inputs the q-matroids of rank `k` on `field^(n-1)` and, as `qm_list_lower`,
    those of rank `k-1`; outputs the canonical representatives of the rank-`k` q-matroids on
    `field^n`, each of them exactly once.

    Non-trivial extensions come from `qm_list`, trivial ones from `qm_list_lower`. Every
    candidate is replaced by the canonical representative of its isomorphism class and
    duplicates are dropped by that representative.
"""

function start_enum_canonical(qm_list::Any, qm_list_lower=[]::Any, info=true::Any)
    length(qm_list) != 0 || error("`qm_list` must contain at least one q-matroid")

    field = base_ring(qm_list[1].groundspace)
    dim = ncols(qm_list[1].groundspace) + 1
    q_rank = rank(qm_list[1].bases[1])

    info && println("Canonicity context for rank $(q_rank) on dimension $(dim)")
    ctx = Canonical_context(field, q_rank, dim)

    found = OrderedDict()
    seen_raw = Set()
    candidate_count = 0
    already_canonical = 0

    function register(indices::Any, selector::Any, id::Any)
        candidate_count += 1
        canonical_indices = Canonical_indices(indices, ctx)
        indices == canonical_indices && (already_canonical += 1)

        if haskey(found, canonical_indices)
            return false
        end
        canonical_bases = AbstractVector{Any}([ctx.qrank_subs[i] for i in canonical_indices])
        merge!(found, OrderedDict([canonical_indices => [selector, canonical_bases, id]]))

        return true
    end

    # ---- first loop: the non-trivial extensions of the rank-k q-matroids --------------
    for (id,elm) in enumerate(qm_list)
        info && println("$id. q-matroid of $(length(qm_list)) in progress")

        candidates = DFS_enum_collect(elm)
        new_classes = 0
        for x in candidates
            indices = Base_indices(x[2], ctx)
            # the same extension can be reached through several selectors
            indices in seen_raw && continue
            push!(seen_raw, indices)
            register(indices, x[1], id) && (new_classes += 1)
        end
        info && println("    $(length(candidates)) leaves, $new_classes new isomorphism classes")
    end

    # ---- second loop: the trivial extensions of the rank-(k-1) q-matroids -------------
    if length(qm_list_lower) != 0
        info && println("Trivial extensions of $(length(qm_list_lower)) q-matroids of rank $(q_rank-1)")

        new_classes = 0
        for (id,elm) in enumerate(qm_list_lower)
            indices = Base_indices(Trivial_extension(elm).bases, ctx)
            indices in seen_raw && continue
            push!(seen_raw, indices)
            register(indices, "trivial extension", -id) && (new_classes += 1)
        end
        info && println("    $new_classes new isomorphism classes")
    else
        @warn "No rank-$(q_rank-1) q-matroids given: the trivial extensions of Algorithm C are skipped and the output will be incomplete."
    end

    if info
        println("---------------------------------------------------------")
        println("$candidate_count distinct extensions, $already_canonical of them already canonical, $(length(found)) isomorphism classes")
    end

    return [v for v in values(found)]
end
################################################################################

###########################################################################################
# Encoding and decoding
###########################################################################################

@doc raw"""
    Q_Matroid_base_enc(base:: Any, kspaces::Any)

    Takes in the bases of a q-matroid of rank k and outputs the 0-1-encoding vector among all k-spaces.
    In particular, if a k-space gets a one if it's a base and zero else. 
"""
function Q_Matroid_base_enc(bases:: Any, kspaces::Any)
    num_k_spaces = length(kspaces)
    enc_vec = ones(Int,num_k_spaces)
    for (id,elm) in enumerate(kspaces)
        if !(elm in bases)
            enc_vec[id]=0
        end
    end

    return enc_vec
end
################################################################################

@doc raw"""
    Q_Matroid_base_dec(enc_bases:: Any, kspaces::Any)

    This takes in the bases 0-1-encoding vector of a q-matroid of rank k and outputs the corresponding bases among all k-spaces. 
"""
function Q_Matroid_base_dec(enc_bases:: Any, kspaces::Any)
    bases = [elm for (id,elm) in enumerate(kspaces) if enc_bases[id] == 1]
    
    return bases
end
################################################################################