using Oscar

###########################################################################################
# Structure to store the reflections in a hyperplane and the hyperplane itself
###########################################################################################
struct ReflectionHyperplane{S, T}
    hyperplane::S
    reflections::Vector{ComplexReflection{T}}
end

# Printing
function Base.show(io::IO, ::MIME"text/plain", h::ReflectionHyperplane)
    print(io, "Reflection hyperplane with ", length(h.reflections), " reflections")
end

###########################################################################################
# Structure to store the hyperplanes in an orbit
###########################################################################################
struct HyperplaneOrbit{S, T}
    hyperplanes::Vector{ReflectionHyperplane{S, T}}
end

# Printing
function Base.show(io::IO, ::MIME"text/plain", o::HyperplaneOrbit)
    print(io, "Hyperplane orbit with ", length(o.hyperplanes), " hyperplanes")
end

###########################################################################################
# Structure to store the orbits of hyperplanes
###########################################################################################
struct ReflectionLibrary{G, S, T}
    group::G
    orbits::Vector{HyperplaneOrbit{S, T}}
    flat_reflections::Vector{ComplexReflection{T}}
end

# Printing
function Base.show(io::IO, ::MIME"text/plain", l::ReflectionLibrary)
    print(io, "Reflection library for ", l.group, " with ", length(l.orbits), " orbits of hyperplanes and ", length(l.flat_reflections), " reflections")
end

###########################################################################################
# Functions needed to construct the reflection library
###########################################################################################

# Function to obtain the order of the eigenvalue of a reflection
function get_eigenvalue_order(r::ComplexReflection)
    ev = eigenvalue(r)
    for i in 1:order(r)
        if ev^i == 1
            return i
        end
    end
end

# Construct the structure ReflectionHyperplane for a given hyperplane and a list of reflections, where the reflections that have the given hyperplane are assigned to it
function build_ReflectionHyperplane(H, reflections)
    # Get the reflections in the given list which have the same hyperplane 
    same_H = Vector{typeof(reflections[1])}()
    for i in 1:length(reflections)
        r = reflections[i]
        if hyperplane(r) == H
            push!(same_H, r)
        end
    end

    # Sort the reflections on the same hyperplane by eigenvalue by order and eigenvalue
    sort!(same_H, by = r -> (order(r), get_eigenvalue_order(r)))
    return ReflectionHyperplane(H, same_H)
end

# Construct the structure HyperplaneOrbit for a given list of hyperplanes, that are saved as ReflectionHyperplane structures with the reflections belonging to them
function build_HyperplaneOrbit(orbit_hyperplanes)
    return HyperplaneOrbit(orbit_hyperplanes)
end

# Construct the structure ReflectionLibrary for a given group, by determining the reflections, grouping them by their hyperplanes and grouping the hyperplanes by their orbits under the group action
function build_ReflectionLibrary(group)
    group_description = describe(group)  # In order to get GAP finding the conjugacy classes, we need to call the describe function on the group
    # Get the conjugacy classes of the group
    classes = conjugacy_classes(group)
    reflslist = []

    for rep in classes
        b, w_data = is_complex_reflection_with_data(matrix(representative(rep)))
        if b
            refl_conj_class = [g for g in rep]  # If one element of the conjugacy class is a reflection, all are, so we can take the whole class and add it to the list of reflections
            for g in refl_conj_class
                b, w_data = is_complex_reflection_with_data(g)
                push!(reflslist, w_data)
            end
        end
    end

    # Sort the list of reflections, corresponding to the "Quick" routine in CHAMP
    refl_map = Dict(matrix(r) => r for r in reflslist)
    sorted_refls = Vector{typeof(reflslist[1])}()
    seen_matrices = Vector{typeof(matrix(reflslist[1]))}()

    for i in 1:ngens(group)  # Go through the generators and take their powers until we have found all reflections which will be sorted by their occurrence in this enumeration
        gen_mat = matrix(gens(group)[i])
        curr = gen_mat
        for j in 1:order(gens(group)[i])
            if haskey(refl_map, curr) && !(curr in seen_matrices)
                push!(sorted_refls, refl_map[curr])
                push!(seen_matrices, curr)
            end
            curr *= gen_mat  # Efficiently move to the next power of the generator
        end
    end

    # If not all reflections were found, the remanining ones are added at the end
    for r in reflslist
        if !(matrix(r) in seen_matrices)
            push!(sorted_refls, r)
        end
    end

    # Define the types for the hyperplanes and the reflections to be able to properly initialize the library hierarchy
    first_refl = sorted_refls[1]
    S = typeof(hyperplane(first_refl))
    T = typeof(first_refl).parameters[1]
    library_hierarchy = Vector{HyperplaneOrbit{S, T}}()
    remaining_refls = copy(sorted_refls)
    
    # Iterate through the reflections in the order determined by the sorting above
    while !isempty(remaining_refls)
        # In order to identify the first orbit, we construct the basis matrix of the hyperplane, which consists of the basis vectors as rows
        curr_refl = remaining_refls[1]
        H_curr = hyperplane(curr_refl)
        H_curr_basis = hyperplane_basis(curr_refl)
        H_basis_list = Vector{typeof(H_curr_basis[1][1])}()
        rank_H = rank(parent(H_curr_basis[1]))
        K = base_ring(curr_refl)
        for i in 1:length(H_curr_basis)
            for j in 1:rank_H
                push!(H_basis_list, H_curr_basis[i][j])
            end
        end
        
        H_basis_matrix = matrix(K, length(H_curr_basis), rank_H, H_basis_list)
        
        # Calculate the orbit of the hyperplane under G
        act = (M, g) -> rref(M * matrix(g))[2]
        X = gset(group, act, [H_basis_matrix])
        orb_hyperplanes = orbit(X, H_basis_matrix)
        orb_list = collect(orb_hyperplanes)

        # Find all reflections and hyperplanesbelonging to this orbit
        orbit_refsl = []
        orbit_hyperplanes = []
        V = vector_space(K, rank_H)
        for r in remaining_refls
            for orb_H in orb_list
                rows = [collect(orb_H[i, :]) for i in 1:nrows(orb_H)]
                H_oh = sub(V, [V(row) for row in rows])[1]  # Get the hyperplane as a subspace to compare it with the hyperplane of the reflection
                push!(orbit_hyperplanes, H_oh)
                if H_oh == hyperplane(r)
                    push!(orbit_refsl, r)
                    break
                end
            end
        end
        filter!(r -> !(r in orbit_refsl), remaining_refls)  # Remove the reflections in this orbit from the remaining reflections
          
        # Within this orbit, group the reflections belonging to the orbit by their hyperplanes
        hyperplane_groups = Vector{HyperplaneOrbit{S, T}}()
        orbit_remaining_refls = copy(orbit_refsl)
        orb_hyperplanes_struct = Vector{ReflectionHyperplane{S, T}}()

        while !isempty(orbit_remaining_refls)
            target_H = hyperplane(orbit_remaining_refls[1])
            
            # All reflections sharing this exact hyperplane
            same_H = build_ReflectionHyperplane(target_H, orbit_remaining_refls)
            filter!(r -> !(r in same_H.reflections), orbit_remaining_refls)  # Remove the reflections sharing this hyperplane from the remaining reflections in this orbit
            push!(orb_hyperplanes_struct, same_H)
        end

        hyperplane_groups = build_HyperplaneOrbit(orb_hyperplanes_struct)
        push!(library_hierarchy, hyperplane_groups)
    end

    # Flatten the library hierarchy and properly type the vectors
    flat_refls = Vector{ComplexReflection{T}}()
    for orb in library_hierarchy
        for hyperplane_group in orb.hyperplanes
            for refl in hyperplane_group.reflections
                push!(flat_refls, refl)
            end
        end
    end

    return ReflectionLibrary(group, library_hierarchy, flat_refls)
end

###########################################################################################
# Getter functions for the reflection library
###########################################################################################

# Get all reflections in the library as a flat list in the order in which they are saved in the libary
function flat_reflections(lib::ReflectionLibrary)
    return lib.flat_reflections
end

# Get the orbits of hyperplanes in the libarary as a list of HyperplaneOrbit structures, where each HyperplaneOrbit is a list of ReflectionHyperplane structures
function hyperplane_orbits(lib::ReflectionLibrary)
    return lib.orbits
end

# Get the hyperplanes in an orbit as a list of ReflectionHyperplane structures, where each ReflectionHyperplane is a hyperplane with the reflections belonging to it
function hyperplanes_in_orbit(orb::HyperplaneOrbit)
    return orb.hyperplanes
end

# Get the reflections belonging to a hyperplane as a list of ComplexReflection structures
function reflections_in_hyperplane(H::ReflectionHyperplane)
    return H.reflections
end

# Get the hyperplane of a ReflectionHyperplane structure
function hyperplane_from_ReflectionHyperplane(H::ReflectionHyperplane)
    return H.hyperplane
end
