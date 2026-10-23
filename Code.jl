using Random

function algebraic_prolongation_system(A::AbstractVector{T}, m::Integer) where T<:ActionPolyRingElem
    D = DifferentialSystem([apply_action(a,[h]) for a in A for h in 0:m])
    return __conversion_algebraic_system(D)
end


function jets(m::Integer)
    _, (a, b) = polynomial_ring(QQ, [:a, :b])
    A = [a]
    B = [b]
    for _ in 1:(m+1)
        p, q = A[end], B[end]
        push!(A, b^2*derivative(p, 1) + a^2*derivative(p, 2))
        push!(B, b^2*derivative(q, 1) + a^2*derivative(q, 2))
    end
    return A, B
end


function reduced_prolongation_system(m::Integer)
    _, (x1, x2) = differential_polynomial_ring(QQ, [:x1, :x2], 1)
    A, B = jets(m)
    E = vcat(
        [x1[j] - evaluate(A[j+1], [x1, x2]) for j in 1:(m+1)],
        [x2[j] - evaluate(B[j+1], [x1, x2]) for j in 1:(m+1)]
    )
    return __conversion_algebraic_system(DifferentialSystem(E))
end


function is_quasi_simple_zero_dimensional(branch::AlgebraicSystem)::Bool
    if branch.quasi_simple !== true
        is_quasi_simple(branch) === true || return false
    end
    E, I = __algebraic_read_system(branch)
    isempty(I) || return false
    return length(E) == ngens(branch.ring)
end


function is_quasi_simple_zero_dimensional(E::AbstractVector{<:MPolyRingElem}, I::AbstractVector{<:MPolyRingElem})
    return is_quasi_simple_zero_dimensional(AlgebraicSystem(E, I))
end


function is_quasi_simple_zero_dimensional(E::AbstractVector{<:MPolyRingElem})
    return is_quasi_simple_zero_dimensional(AlgebraicSystem(E))
end


function count_thomas_points(S::AlgebraicSystem)
    branches = thomas_decomposition(S)
    return count_thomas_points(branches)
end


function count_thomas_points(branches::AbstractVector)
    total = big(0)
    for (i, S) in enumerate(branches)
        S.simple === true || error("The branch $i is not simple")
        E, I = system_to_vectors(S)
        isempty(I) || error("The branch $i is not zero-dimensional: it contains inequations")
        n = ngens(S.ring)
        leaders = Int[]
        count_i = big(1)
        for f in E
            idx = var_index(__algebraic_leader(f))
            push!(leaders, idx)
            count_i *= degree(f, idx)
        end
        sort(leaders) == collect(1:n) ||
            error("The branch $i is not zero-dimensional: some variable is not the leader
                of any equation")
        total += count_i
    end
    return total
end


function random_slices(A, B, r; bound=5)
    coeff() = rand(r, -bound:bound)
    P = A[end] + coeff()*one(A[1])
    Q = B[end] + coeff()*one(B[1])
    for j in 1:(length(A)-1)
        P += coeff()*A[j] + coeff()*B[j]
        Q += coeff()*A[j] + coeff()*B[j]
    end
    return P, Q
end


function check_slice(P, Q, m::Integer)
    d = m+2
    total_degree(P) == d || error("P does not have the correct degree $d")
    total_degree(Q) == d || error("Q does not have the correct degree $d")
    F = homogeneous_part(P, d)
    G = homogeneous_part(Q, d)
    F_h = homogeneous_part(P, d-1)
    G_h = homogeneous_part(Q, d-1)
    H = gcd(F, G)
    squarefree_H = is_constant(gcd(gcd(H, derivative(H, 1)), derivative(H, 2)))
    Ja = derivative(G, 1)*F_h - derivative(F, 1)*G_h
    Jb = derivative(G, 2)*F_h - derivative(F, 2)*G_h
    bad = gcd(gcd(H, Ja), Jb)
    transverse_infinity = is_constant(bad)
    coprime = is_constant(gcd(P, Q))
    upper_bound = squarefree_H ? d*d-total_degree(H) : nothing
    T = thomas_decomposition(AlgebraicSystem([P, Q]); factorization=false)
    obtained = count_thomas_points(T)
    certified = coprime && squarefree_H && transverse_infinity && obtained == upper_bound
    return (certified=certified, thomas_points=obtained)
end


function homogeneous_part(f, k::Integer)
    h = zero(f)
    for (c, mon) in zip(coefficients(f), monomials(f))
        if total_degree(mon) == k
            h += c*mon
        end
    end
    return h
end


function test_conjecture(m::Integer; bound::Integer=20,
                         max_attempts::Integer=30,
                         seed::Integer=20261016)::Bool
                         m >= 0 || throw(ArgumentError("m must be non-negative"))
    A, B = jets(m)
    rng = MersenneTwister(seed)
    conjectured = big(m+2)^2 - (mod(m, 3) == 1 ? 2 : 0)
    for _ in 1:max_attempts
        P, Q = random_slices(A, B, rng; bound=bound)
        result = check_slice(P, Q, m)
        result.certified || continue
        return result.thomas_points == conjectured
    end
    error("Could not certify a generic slice for m=$m after $max_attempts attempts")
end


function test_conjecture_fast(m::Integer)::Bool
    m >= 0 || throw(ArgumentError("m must be non-negative"))
    A, B = jets(m)
    F, G = A[end], B[end]
    U, V = A[end-1], B[end-1]
    H = gcd(F, G)
    squarefree_H = is_constant(gcd(gcd(H, derivative(H, 1)), derivative(H, 2)))
    squarefree_H || error("The GCD is not square-free for m=$m")
    J1 = derivative(G, 1)*U - derivative(F, 1)*V
    J2 = derivative(G, 2)*U - derivative(F, 2)*V
    transverse_infinity = is_constant(gcd(gcd(H, J1), J2))
    transverse_infinity || error("Transversality at infinity could not be verified for m=$m")
    computed_degree = big(m+2)^2 - total_degree(H)
    conjectured_degree = big(m+2)^2 - (mod(m, 3) == 1 ? 2 : 0)
    return computed_degree == conjectured_degree
end


function test_conjecture_fast_all(N::Integer)::Bool
    N >= 1 || throw(ArgumentError("N must be positive"))
    m = 1
    while m <= N
        if !test_conjecture_fast(m)
            println("Conjecture failed for m = $m")
            return false
        end
        println("m = $m: OK")
        m += 1
    end
    return true
end


function final_polynomial_sequence(n::Integer)
    n >= 0 || throw(ArgumentError("n must be non-negative"))
    R, t = polynomial_ring(ZZ, :t)
    p = R(1)
    for l in 0:(n-1)
        if mod(l, 3) == 0
            p = (l+1)*p + 3*(1-t)*derivative(p)
        elseif mod(l, 3) == 1
            p = (2+(l-1)*t)*p + 3*t*(1-t)*derivative(p)
        else
            p = (1+l*t)*p + 3*t*(1-t)*derivative(p)
        end
    end
    past = R(1)
    for l in 0:(n-1)
        if mod(l, 3) == 0
            past = (1+l*t)*past + 3*t*(1-t)*derivative(past)
        elseif mod(l, 3) == 1
            past = (l+1)*past + 3*(1-t)*derivative(past)
        else
            past = (2+(l-1)*t)*past + 3*t*(1-t)*derivative(past)
        end
    end
    return p, past
end


#######################################################
####### GENERALIZATION TO x1'=x2^n, x2'=x1^n
#######################################################


function jets(m::Integer; exponent::Integer=2)
    m >= 0 || throw(ArgumentError("m must be nonnegative"))
    exponent >= 2 || throw(ArgumentError("exponent must be at least 2"))
    _, (a, b) = polynomial_ring(QQ, [:a, :b])
    A = [a]
    B = [b]
    for _ in 1:(m+1)
        p, q = A[end], B[end]
        push!(A, b^exponent*derivative(p, 1) +
                 a^exponent*derivative(p, 2))
        push!(B, b^exponent*derivative(q, 1) +
                 a^exponent*derivative(q, 2))
    end
    return A, B
end


function reduced_prolongation_system(m::Integer; exponent::Integer=2)
    _, (x1, x2) = differential_polynomial_ring(QQ, [:x1, :x2], 1)
    A, B = jets(m; exponent=exponent)
    E = vcat(
        [x1[j] - evaluate(A[j+1], [x1, x2]) for j in 1:(m+1)],
        [x2[j] - evaluate(B[j+1], [x1, x2]) for j in 1:(m+1)]
    )
    return __conversion_algebraic_system(DifferentialSystem(E))
end


function check_slice(P, Q, m::Integer; exponent::Integer=2)
    d = 1 + (exponent-1)*(m+1)
    total_degree(P) == d || error("P does not have the correct degree $d")
    total_degree(Q) == d || error("Q does not have the correct degree $d")
    F = homogeneous_part(P, d)
    G = homogeneous_part(Q, d)
    F_h = homogeneous_part(P, d-1)
    G_h = homogeneous_part(Q, d-1)
    H = gcd(F, G)
    squarefree_H = is_constant(gcd(gcd(H, derivative(H, 1)), derivative(H, 2)))
    r = Int(total_degree(H))
    Ja = derivative(G, 1)*F_h - derivative(F, 1)*G_h
    Jb = derivative(G, 2)*F_h - derivative(F, 2)*G_h
    bad = gcd(gcd(H, Ja), Jb)
    transverse_infinity = is_constant(bad)
    coprime = is_constant(gcd(P, Q))
    upper_bound = squarefree_H ? d*d-r : nothing
    T = thomas_decomposition(AlgebraicSystem([P, Q]); factorization=false)
    obtained = count_thomas_points(T)
    certified = coprime && squarefree_H && transverse_infinity && obtained == upper_bound
    return (
        m=m, degree_d=d, points_at_infinity=r, infinity_gcd=H,
        bad_infinity_factor=bad, infinity_squarefree=squarefree_H,
        transverse_infinity=transverse_infinity, coprime=coprime,
        bezout_upper_bound=upper_bound, thomas_points=obtained,
        branches=length(T), certified=certified
    )
end


function conjectured_degree(m::Integer; exponent::Integer=2)
    m >= 0 || throw(ArgumentError("m must be non-negative"))
    if exponent == 2
        return big(m+2)^2 - (mod(m, 3) == 1 ? 2 : 0)
    elseif exponent == 3
        return big(2*m+3)^2 - (mod(m, 4) in (1, 2) ? 8 : 0)
    else
        throw(ArgumentError("No conjectured formula for exponent=$exponent"))
    end
end


function test_conjecture(m::Integer; exponent::Integer=2,
                         bound::Integer=20,
                         max_attempts::Integer=30,
                         seed::Integer=20261016)::Bool
    m >= 0 || throw(ArgumentError("m must be nonnegative"))
    A, B = jets(m; exponent=exponent)
    rng = MersenneTwister(seed)
    expected = conjectured_degree(m; exponent=exponent)
    maximum_obtained = big(0)
    for _ in 1:max_attempts
        P, Q = random_slices(A, B, rng; bound=bound)
        T = thomas_decomposition(AlgebraicSystem([P, Q]); factorization=false)
        obtained = count_thomas_points(T)
        maximum_obtained = max(maximum_obtained, obtained)
        obtained == expected && return true
    end
    println("m = $m: maximum observed = $maximum_obtained, expected = $expected")
    return false
end


function count_slice_points_fast(P, Q)
    a, b = gens(parent(P))
    d = Int(total_degree(P))
    F = homogeneous_part(P, d)
    G = homogeneous_part(Q, d)
    # Avoid points at infinity in the eliminated direction
    iszero(evaluate(F, [-1, 1])) &&
        error("The chosen projection is unsuitable for P")
    iszero(evaluate(G, [-1, 1])) &&
        error("The chosen projection is unsuitable for Q")
    Ps = evaluate(P, [a-b, b])
    Qs = evaluate(Q, [a-b, b])
    R = resultant(Ps, Qs, 2)
    iszero(R) && return nothing
    is_constant(gcd(R, derivative(R, 1))) ||
        return nothing
    return Int(degree(R, 1))
end

##########################################################################################
##########################################################################################

### Test the extension of the conjecture with exponent n>=2 and for all prolongations up to order max_l
function test_prolongation_gcd(n::Integer, max_m::Integer)::Bool
    println("$n")
    _, (a, b) = polynomial_ring(QQ, [:a, :b])
    A, B = a, b
    an, bn = a^n, b^n
    for m in 0:max_m
        A, B = (
            bn*derivative(A, 1) + an*derivative(A, 2),
            bn*derivative(B, 1) + an*derivative(B, 2)
        )
        r = mod(m, n+1)
        e = (1 <= r <= n-1) ? n-r : 0
        is_associated(gcd(A, B), (a*b)^e) || return false
    end
    return true
end

function test_prolongation_gcd_all(;
    n_min::Integer=2,
    n_max::Integer=100,
    max_m::Integer=1000
)::Bool
    return all(
        test_prolongation_gcd(n, max_m)
        for n in n_min:n_max
    )
end