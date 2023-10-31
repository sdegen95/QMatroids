################################################################################
##  Enumeration of q-matroids
################################################################################
using Oscar
using DataStructures
using Combinatorics
using Graphs
using GraphPlot
using Compose
using Random
using InvertedIndices
include("./helper_functions.jl")


@doc raw"""
    Diamond_prop(indeps::AbstractVector{fpMatrix}, deps::AbstractVector{fpMatrix}, all_diams=nothing::Union{Nothing,AbstractVector{AbstractVector{fpMatrix}}})

    Returns if the union list of `indeps` and `deps` satisfies the q-matroid diamond condtion.

    For the `all_diams`-option one can insert a list of all diamonds of the ambient space.

    Note: This is required to speed up the computations in the below enumeration functions.
"""
function Diamond_prop(field::Nemo.fpField, indeps::AbstractVector{fpMatrix}, deps::AbstractVector{fpMatrix}, all_diams=nothing::Union{Nothing,AbstractVector{AbstractVector{fpMatrix}}})
    holds = true

    # Put all current spaces together in one list
    all_current_spaces = union(indeps,deps)
    
    # Sort them w.r.t to their subspace dimension
    sort!(all_current_spaces, by = x -> subspace_dim(field,x))

    # Create all possible diamonds
    if isnothing(all_diams)
        diams = diamond_list(field,all_current_spaces)
    else
        # Here we put in all possible diamonds of the vector_space, not only those in the current spaces
        # Check which of all the diamonds of the v.s. is in the current_spaces_list
        diams = []
        for elm in all_diams
            if issubset(elm,all_current_spaces)
                push!(diams,elm)
            end
        end
    end

    # Check if all currently possible diamonds satisfy the one of the four possible options
    for diam in diams
        sort!(diam, by = x -> subspace_dim(field,x))
        overall_count = 0
        if diam[1] in indeps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in deps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in deps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                elseif elm == diam[length(diam)]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # mixed diamond
            count = 0
            for elm in diam
                if elm != diam[1] && elm != diam[length(diam)]
                    if elm in indeps
                        continue
                    elseif elm in deps
                        count += 1
                    end
                elseif elm == diam[length(diam)]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
                if count > 1
                    overall_count += 1
                    break
                end
            end

        elseif diam[1] in deps
            # One diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # zero diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # prime diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count += 1
                        break
                    else
                        continue
                    end
                end
            end
            # mixed diamond
            for elm in diam
                if elm != diam[1]
                    if elm in indeps
                        overall_count +=1
                        break
                    else
                        continue
                    end
                end
            end
        end

        if overall_count >= 4
            holds = false
            break
        else
            continue
        end
    end

    
    return holds
end