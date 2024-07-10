using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices
include("./enumeration.jl")

##############################################################################################
# Struct's
##############################################################################################

struct Vs_numbers 
    num_all_subs::Oscar.IntegerUnion
    num_leftovers::Oscar.IntegerUnion
    char::Oscar.IntegerUnion
    dim::Oscar.IntegerUnion
end

struct Vs_encodings
    lo_dict::AbstractDict
    en_all_diams::AbstractVector{AbstractVector{AbstractVector{Int}}}
    en_all_spaces::AbstractVector{AbstractVector{Int}}
end

struct Node
    indeps::AbstractVector{AbstractVector{Int}}
    deps::AbstractVector{AbstractVector{Int}}
    counter::Oscar.IntegerUnion
end

struct Resultlist_entry
    indeps::AbstractVector{AbstractVector{Int}}
    deps::AbstractVector{AbstractVector{Int}}
    maxis::AbstractVector{AbstractVector{Int}}
end


##############################################################################################
# Helper function
##############################################################################################


function findall_Node(Current_node::Node, Stack::AbstractVector)
    Current_Node_list = [Set(Current_node.indeps),Set(Current_node.deps),Current_node.counter]

    Remove_indicies = []
    for (id,Node) in enumerate(Stack)
        Node_list = [Set(Node.indeps),Set(Node.deps),Node.counter]
        if Node_list == Current_Node_list
            push!(Remove_indicies,id)
        end
    end

    return Remove_indicies
end

function unique_Result_list(Result_list::AbstractVector)
    helper_list = [[entry.indeps,entry.deps,entry.maxis] for entry in Result_list]
    unique!(helper_list)
    New_Result_list = [Resultlist_entry(elm[1],elm[2],elm[3]) for elm in helper_list]

    return New_Result_list
end

# function is_in_Result_list(NODE::Node, Result_list::AbstractVector)
#     is_not_in = true
#     maxis = [NODE.indeps[x] for x in findall(y->length(y)==maximum(length,NODE.indeps),NODE.indeps)]
#     possibleentry_list = [NODE.indeps,NODE.deps,maxis]
#     resultlist_list = [[entry.indeps,entry.deps,entry.maxis] for entry in Result_list]

#     if possibleentry_list in resultlist_list
#         is_not_in = false
#     end

#     return is_not_in, maxis
# end



##############################################################################################
# The algorithm (enumeration of rank-2 q-matroids)
##############################################################################################


function EN_create_neighbours(NODE::Node,
                              Vs_ens::Vs_encodings,
                              Vs_nums::Vs_numbers)

    # Increase the depth of the tree
    New_counter = NODE.counter + 1

    # Get the encoded space which are not assigned yet
    con_sp = collect(values(Vs_ens.lo_dict))[New_counter][2]
    compl_list = [elm for elm in con_sp if (!(elm in NODE.indeps) && !(elm in NODE.deps))]

    # Helperlist
    two_sp_cont = [x for x in con_sp if length(x)==q_binomcoeff(Vs_nums.char,2,1)+1]
    two_sp_not_compl = [x for x in two_sp_cont if !(x in compl_list)]
    
    # Decide the possible options
    En_Options = []
    for i in range(1,Vs_nums.dim)
    # 1. options: 0-dim loop space
        if i == 1
            if two_sp_cont != []
                right_count = 0
                for elm in two_sp_cont
                    if elm in NODE.indeps
                        right_count += 1
                    elseif elm in compl_list
                        right_count += 1
                    end
                end
                
                if right_count == q_binomcoeff(Vs_nums.char,Vs_nums.dim-1,1)
                    New_Indeps_list = copy(NODE.indeps) 
                    New_Deps_list = copy(NODE.deps)
                    for elm in compl_list
                        push!(New_Indeps_list,elm)
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                        en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                        push!(En_Options,en_option)
                    end
                end
            end
    # 2. options: 1-dim loop space
        elseif i == 2
            if two_sp_not_compl != []
                if !(two_sp_not_compl[1] in NODE.deps)
                    for elmx in compl_list
                        New_Indeps_list = copy(NODE.indeps) 
                        New_Deps_list = copy(NODE.deps)
                        push!(New_Deps_list,elmx)
                        for elmy in compl_list
                            if elmy != elmx
                                push!(New_Indeps_list,elmy)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                            en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                            push!(En_Options,en_option)
                        end
                    end
                end
            else
                for elmx in compl_list
                    New_Indeps_list = copy(NODE.indeps) 
                    New_Deps_list = copy(NODE.deps)
                    push!(New_Deps_list,elmx)
                    for elmy in compl_list
                        if elmy != elmx
                            push!(New_Indeps_list,elmy)
                        end
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                        en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                        push!(En_Options,en_option)
                    end
                end
            end
    # 3. options: 1-dim loop space (already assigned element)
        elseif i == 3
            inters = intersect(two_sp_not_compl,NODE.deps)
            if inters != []
                for elmx in inters
                    New_Indeps_list = copy(NODE.indeps) 
                    New_Deps_list = copy(NODE.deps)
                    for elmy in compl_list
                        push!(New_Indeps_list,elmy)
                    end
                    if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                        en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                        push!(En_Options,en_option)
                    end
                end
            end
    # 4. options: 2-dim loop space
        elseif i == 4
            con_diams = [x for x in Vs_ens.en_all_diams if issubset(x,con_sp) && length(x[1])==2]
            if con_diams != []
                for diam in con_diams
                    twos = [x for x in diam if length(x)==q_binomcoeff(Vs_nums.char,2,1)+1]
                    if issubset(twos,compl_list)
                        New_Indeps_list = copy(NODE.indeps) 
                        New_Deps_list = copy(NODE.deps)
                        for elm in twos
                            push!(New_Deps_list,elm)
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                            en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                            push!(En_Options,en_option)
                        end
                    elseif intersect(twos,NODE.deps) != []
                        New_Indeps_list = copy(NODE.indeps) 
                        New_Deps_list = copy(NODE.deps)
                        for elm in twos
                            if !(elm in NODE.deps)
                                push!(New_Deps_list,elm)
                            end
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                            en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                            push!(En_Options,en_option)
                        end
                    end
                end
            end
    # 5. options: 3-dim loop space
        elseif i == 5
            new_con_sp = sort(AbstractVector{AbstractVector{Int}}([x for x in con_sp if length(x)<=q_binomcoeff(Vs_nums.char,4,1)+1]),by = x->length(x))
            con_3_int = encoded_k_interval(new_con_sp,Vs_nums.char,3,Vs_ens.en_all_spaces)
            if con_3_int != []
                for int in con_3_int
                    sort!(int,by = x->length(x))
                    twos = [x for x in int if length(x)==q_binomcoeff(Vs_nums.char,2,1)+1]
                    if issubset(twos,compl_list)
                        New_Indeps_list = copy(NODE.indeps) 
                        New_Deps_list = copy(NODE.deps)
                        for elm in twos
                            push!(New_Deps_list,elm)
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                            en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                            push!(En_Options,en_option)
                        end
                    elseif intersect(twos,NODE.deps) != []
                        New_Indeps_list = copy(NODE.indeps) 
                        New_Deps_list = copy(NODE.deps)
                        for elm in twos
                            if !(elm in NODE.deps)
                                push!(New_Deps_list,elm)
                            end
                        end
                        for elm in compl_list
                            if !(elm in twos)
                                push!(New_Indeps_list,elm)
                            end
                        end
                        if En_Diamond_prop(New_Indeps_list,New_Deps_list,Vs_ens.en_all_diams)
                            en_option = Node(New_Indeps_list,New_Deps_list,New_counter)
                            push!(En_Options,en_option)
                        end
                    end
                end
            end
        end
    end

    return unique!(En_Options)

end

function EN_LIFO(Current_node::Node,
                 Stack::AbstractVector,
                 Result_list::AbstractVector,
                 V_Results::AbstractVector,
                 Vs_ens::Vs_encodings,
                 Vs_nums::Vs_numbers)

    # Calculate the neighbors of the current node
    neighbours = EN_create_neighbours(Current_node,Vs_ens,Vs_nums)

    # Insert all neigbours of the current node before the node in the stack list
    if length(neighbours) != 0
        for neighbour in neighbours
            insert!(Stack,1,neighbour)
        end
    end

    # Remove the current node  and all similar nodes from the stack
    Remove_indicies = findall_Node(Current_node,Stack)
    deleteat!(Stack,Remove_indicies)

    # Gone recursivly through the stack
    for node in Stack
        if node.counter < Vs_nums.num_leftovers && length(node.indeps) + length(node.deps) < Vs_nums.num_all_subs
            EN_LIFO(node,Stack,Result_list,V_Results,Vs_ens,Vs_nums)

        elseif node.counter == Vs_nums.num_leftovers || length(node.indeps) + length(node.deps) == Vs_nums.num_all_subs
            if node in V_Results
                continue
            else
                #maxis = [node.indeps[x] for x in findall(y->length(y)==maximum(length,node.indeps),node.indeps)]
                entry = Resultlist_entry(node.indeps,node.deps,maxis)
                push!(Result_list,entry)
                push!(V_Results,node)
            end
        end
    end

end

function EN_q_matroid_DFS(QM::Q_Matroid)
    # Define all necesssary variables
    Indeps_list = AbstractVector{AbstractVector{Int}}([])
    Deps_list = AbstractVector{AbstractVector{Int}}([])
    Stack = []
    Result_list = []
    V_Results = []
    Counter = 0

    # Get the Indeps, Deps and Dimension of the Input
    Init_Dim = ncols(QM.groundspace)
    Init_Field = base_ring(QM.groundspace)
    Init_char = Int(characteristic(Init_Field))
    Init_Indeps = Q_Matroid_Independentspaces(QM)
    Init_Deps = Q_Matroid_Dependentspaces(QM)

    # Transform the intial Input
    Trans_Indeps = standard_embedding_higher_dim(Init_Indeps,Init_Dim+1)
    if Init_Deps != []
        Trans_Deps = standard_embedding_higher_dim(Init_Deps,Init_Dim+1)
    else
        Trans_Deps = AbstractVector{fpMatrix}([])
    end

    # Compute all spaces of the ambient space
    All_sp = sort(all_subspaces(Init_Field,Init_Dim+1), by = x -> rank(x))
    Num_all_sp = length(All_sp)
    Ones_dict = OrderedDict([id-1=>elm for (id,elm) in enumerate(All_sp) if rank(elm)==1])

    # Encode the tranformed spaces 
    En_all_sp = sub_encoding(All_sp,Ones_dict)
    En_one_sp = [elm for elm in En_all_sp if length(elm)==2]
    En_Trans_Indeps = sub_encoding(Trans_Indeps,Ones_dict)
    if Trans_Deps != []
        En_Trans_Deps = sub_encoding(Trans_Deps,Ones_dict)
    else
        En_Trans_Deps = AbstractVector{AbstractVector{Int}}([])
    end

    # Create all encoded diamonds of the encoded ambient space
    En_all_diams = encoded_k_interval(En_all_sp,Init_char,2,En_all_sp)

    # Fill Indeps and Deps Lists with the encoded tranformed Init-Input
    for elm in En_Trans_Indeps
        push!(Indeps_list,elm)
    end
    for elm in En_Trans_Deps
        push!(Deps_list,elm)
    end

    # Create the `LO_dict` and declare them all to be independent
    LO_dict = OrderedDict([])
    index = 1
    for elm in En_one_sp
        if (!(elm in Indeps_list) && !(elm in Deps_list))
            merge!(LO_dict,Dict(index=>[elm,encoded_containments_fix_space(elm,En_all_sp)]))
            index += 1
        end
    end
    #LO_dict = OrderedDict([id => [elm,encoded_containments_fix_space(elm,En_all_sp)] for (id,elm) in enumerate(En_one_sp) if (!(elm in Indeps_list) && !(elm in Deps_list))])
    union!(Indeps_list,[x[1] for x in collect(values(LO_dict))])
    Num_leftovers = length(LO_dict)

    # Declare all encoded spaces which have dim. greate equal 2 as dependent
    En_dim_two = q_binomcoeff(Init_char,2,1)+1 
    Bad_en_dims = [1,2,En_dim_two]
    for elm in En_all_sp
        if !(length(elm) in Bad_en_dims) && !(elm in Deps_list) && !(elm in Indeps_list)
            push!(Deps_list,elm)
        end
    end

    # Looking for loops, so all encoded dim.-2 spaces can be declared dependent
    for elm in Deps_list
        if length(elm) == 2
            super_sp = [x for x in encoded_containments_fix_space(elm,En_all_sp) if (length(x)==En_dim_two && !(x in Deps_list) && !(x in Indeps_list))]
            union!(Deps_list,super_sp)
        end
    end

    # Instantiate all strut's
    Init_node = Node(Indeps_list,Deps_list,Counter)
    Vs_nums = Vs_numbers(Num_all_sp,Num_leftovers,Init_char,Init_Dim+1)
    Vs_ens = Vs_encodings(LO_dict,En_all_diams,En_all_sp)

    # Now push the `Init_node` into the stack
    push!(Stack,Init_node)

    # Start the DFS-Algo
    EN_LIFO(Init_node,Stack,Result_list,V_Results,Vs_ens,Vs_nums)

    return unique_Result_list(Result_list)
    #return Result_list

end