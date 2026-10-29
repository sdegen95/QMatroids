################################################################################
##  Representability check for q-matroids
################################################################################

include("helper_functions.jl")

###########################################################################################
# !!!Any matrix you input in a function/method needs to be in RREF!!!
###########################################################################################

################################################################################
##  Subspace cache
################################################################################
const _SUBSPACE_CACHE = Dict{Tuple{Any,Int,Int},Any}()

@doc raw"""
    cached_subspaces_fix_dim(field, k, n)

    Memoized `subspaces_fix_dim`. Returns the cached vector itself.
    Use `clear_subspace_cache!()` to clear the memory.
"""
function cached_subspaces_fix_dim(field, k, n)
    get!(_SUBSPACE_CACHE, (field, Int(k), Int(n))) do
        subspaces_fix_dim(field, k, n)
    end
end

clear_subspace_cache!() = (empty!(_SUBSPACE_CACHE); nothing)

################################################################################
##  Normalization
################################################################################

@doc raw"""
    pivot_basis_columns(Bases::Any, q_rank::Int)

    Returns the columns of the leftmost basis in *coordinate form*, i.e., an RREF matrix that is
    a selection of standard basis vectors.

    Such a basis `B` satisfies `G*transpose(B) == G[:, cols]`, so normalizing a
    representation by `G -> (G*transpose(B))^-1 * G` puts the identity into exactly
    those columns.

    Throws if no basis is in coordinate form.
"""
function pivot_basis_columns(Bases::Any, q_rank::Int)
    pivots = nothing
    for basis in Bases
        indices = findall(!iszero, Array(basis))
        length(indices) == q_rank || continue
        cols = sort!([idx[2] for idx in indices])
        if pivots === nothing || cols < pivots
            pivots = cols
        end
    end
    pivots === nothing && throw(ArgumentError(
        "no basis in coordinate form -- cannot normalize the representing " *
        "matrix (the input may not be a q-matroid)"))
    return pivots
end

################################################################################
##  Representability
################################################################################

@doc raw"""
    is_representable_sat(QM::Q_Matroid; cache::Bool=true)

    Return `(; representable::Bool, nsat::Int, ideal)` -- whether `QM` is
    representable over some extension of its prime field, how many saturation steps
    were needed, and the final ideal (`nothing` when an exact certificate settled the
    question without any Groebner computation).

    Decides `I_dep : (prod det_B)^inf != (1)` by saturating one basis minor at a time.

    Note this only decides representability over *some* extension of the ground field of `QM` 
"""
function is_representable_sat(QM::Q_Matroid; cache::Bool=true)
    Bases = QM.bases
    isempty(Bases) && throw(ArgumentError("q-matroid has no bases"))

    dim    = ncols(Bases[1])
    q_rank = rank(Bases[1])

    # Rank 0: the zero matrix represents it.
    q_rank == 0 && return (representable = true, nsat = 0, ideal = nothing)

    Field = base_ring(Bases[1])
    prime = finite_field(Int(characteristic(Field)), 1, "a")[1]

    pivots = pivot_basis_columns(Bases, q_rank)
    free   = [(i, c) for c in 1:dim if !(c in pivots) for i in 1:q_rank]

    R, x   = polynomial_ring(prime, max(length(free), 1))

    all_k     = cache ? cached_subspaces_fix_dim(Field, q_rank, dim) :
                        subspaces_fix_dim(Field, q_rank, dim)
    basis_set = Set(Bases)
    
    nb_mats = [transpose(matrix(prime, Array(space)))
               for space in all_k if !(space in basis_set)]
    b_mats  = [transpose(matrix(prime, Array(basis))) for basis in Bases]

    # Fill G, then repeatedly drop every variable that a *linear* dependency forces to zero.  
    live = trues(length(free))
    local G
    while true
        G = matrix_space(R, q_rank, dim)(0)
        for (j, c) in enumerate(pivots)
            G[j, c] = one(R)
        end
        for (k, (i, c)) in enumerate(free)
            live[k] && (G[i, c] = x[k])
        end

        forced = false
        for space_mat in nb_mats
            p = det(G * space_mat)
            (length(terms(p)) == 1 && total_degree(p) == 1) || continue
            k = findfirst(>(0), first(exponents(p)))
            if k !== nothing && k <= length(free) && live[k]
                live[k] = false
                forced  = true
            end
        end
        forced || break
    end

    dep_polys = [det(G * M) for M in nb_mats]
    bas_polys = [det(G * M) for M in b_mats]

    # Exact certificates
    # A basis whose minor vanishes identically can never be made nonzero.
    any(iszero, bas_polys) &&
        return (representable = false, nsat = 0, ideal = nothing)
    # A dependency whose minor is a nonzero constant can never be made zero.
    any(p -> !iszero(p) && is_constant(p), dep_polys) &&
        return (representable = false, nsat = 0, ideal = nothing)

    gens = eltype(dep_polys)[p for p in dep_polys if !iszero(p)]

    # Check if there are no dependent polynomials 
    # No dependency constraints: V(I_dep) is all of affine space and R is a
    # domain, hence saturating the zero ideal by anything nonzero leaves it zero.
    isempty(gens) && return (representable = true, nsat = 0, ideal = nothing)

    I = ideal(R, gens)
    nsat = 0
    for p in bas_polys
        is_constant(p) && continue          # units saturate away trivially
        I = saturation(I, ideal(R, [p]))
        nsat += 1
        # Once the saturation is the unit ideal it stays the unit ideal.
        is_one(I) && return (representable = false, nsat = nsat, ideal = I)
    end

    return (representable = !is_one(I), nsat = nsat, ideal = I)
end