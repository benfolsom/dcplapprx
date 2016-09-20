export combinations,
       CoolLexCombinations,
       multiset_combinations,
       with_replacement_combinations,
       pre_glex,
       glexer,
       multprod

#The Combinations iterator

immutable Combinations{T}
    a::T
    t::Int
end

start(c::Combinations) = [1:c.t;]
function next(c::Combinations, s)
    comb = [c.a[si] for si in s]
    if c.t == 0
        # special case to generate 1 result for t==0
        return (comb,[length(c.a)+2])
    end
    s = copy(s)
    for i = length(s):-1:1
        s[i] += 1
        if s[i] > (length(c.a) - (length(s)-i))
            continue
        end
        for j = i+1:endof(s)
            s[j] = s[j-1]+1
        end
        break
    end
    (comb,s)
end
done(c::Combinations, s) = !isempty(s) && s[1] > length(c.a)-c.t+1

length(c::Combinations) = binomial(length(c.a),c.t)

eltype{T}(::Type{Combinations{T}}) = Vector{eltype(T)}

"Generate all combinations of `n` elements from an indexable object. Because the number of combinations can be very large, this function returns an iterator object. Use `collect(combinations(array,n))` to get an array of all combinations.
"
function combinations(a, t::Integer)
    if t < 0
        # generate 0 combinations for negative argument
        t = length(a)+1
    end
    Combinations(a, t)
end


"""
generate combinations of all orders, chaining of order iterators is eager,
but sequence at each order is lazy
"""
combinations(a) = chain([combinations(a,k) for k=1:length(a)]...)



# cool-lex combinations iterator

"""
Produces (n,k)-combinations in cool-lex order

Implements the cool-lex algorithm to generate (n,k)-combinations
@article{Ruskey:2009fk,
	Author = {Frank Ruskey and Aaron Williams},
	Doi = {10.1016/j.disc.2007.11.048},
	Journal = {Discrete Mathematics},
	Month = {September},
	Number = {17},
	Pages = {5305-5320},
	Title = {The coolest way to generate combinations},
	Url = {http://www.sciencedirect.com/science/article/pii/S0012365X07009570},
	Volume = {309},
	Year = {2009}}
"""
immutable CoolLexCombinations
    n :: Int
    t :: Int
end

immutable CoolLexIterState{T<:Integer}
    R0:: T
    R1:: T
    R2:: T
    R3:: T
end

function start(C::CoolLexCombinations)
    if C.n < 0
        throw(DomainError())
    end
    if C.t ≤ 0
        throw(DomainError())
    end

    #What integer size should I use?
    if C.n < 8sizeof(Int)
        T = Int
    else
        T = BigInt
    end

    CoolLexIterState{T}(0, 0, T(1) << C.n, (T(1) << C.t) - 1)
end

function next(C::CoolLexCombinations, S::CoolLexIterState)
    R0 = S.R0
    R1 = S.R1
    R2 = S.R2
    R3 = S.R3

    R0 = R3 & (R3 + 1)
    R1 = R0 $ (R0 - 1)
    R0 = R1 + 1
    R1 &= R3
    R0 = max((R0 & R3) - 1, 0)
    R3 += R1 - R0

    _cool_lex_visit(S.R3), CoolLexIterState(R0, R1, R2, R3)
end

#Converts an integer bit pattern X into a subset
#If X & 2^k == 1, then k is in the subset
function _cool_lex_visit(X::Int)
  subset = Int[]
  n=1
  while X != 0
    if X & 1 == 1 push!(subset, n) end
    X >>= 1
    n += 1
  end
  subset
end

done(C::CoolLexCombinations, S::CoolLexIterState) = (S.R3 & S.R2 != 0)

length(C::CoolLexCombinations) = max(0, binomial(C.n, C.t))


immutable MultiSetCombinations{T}
    m::T
    f::Vector{Int}
    t::Int
    ref::Vector{Int}
end

eltype{T}(::Type{MultiSetCombinations{T}}) = Vector{eltype(T)}

function length(c::MultiSetCombinations)
    t = c.t
    if t > length(c.ref)
        return 0
    end
    p = [1; zeros(Int,t)]
    for i in 1:length(c.f)
        f = c.f[i]
        if i == 1
            for j in 1:min(f, t)
                p[j+1] = 1
            end
        else
            for j in t:-1:1
                p[j+1] = sum(p[max(1,j+1-f):(j+1)])
            end
        end
    end
    return p[t+1]
end

function multiset_combinations{T<:Integer}(m, f::Vector{T}, t::Integer)
    length(m) == length(f) || error("Lengths of m and f are not the same.")
    ref = length(f) > 0 ? vcat([[i for j in 1:f[i] ] for i in 1:length(f)]...) : Int[]
    if t < 0
        t = length(ref) + 1
    end
    MultiSetCombinations(m, f, t, ref)
end

"generate all combinations of size t from an array a with possibly duplicated elements."
function multiset_combinations{T}(a::T, t::Integer)
    m = unique(collect(a))
    f = Int[sum([c == x for c in a]) for x in m]
    multiset_combinations(m, f, t)
end

start(c::MultiSetCombinations) = c.ref
function next(c::MultiSetCombinations, s)
    ref = c.ref
    n = length(ref)
    t = c.t
    changed = false
    comb = [c.m[s[i]] for i in 1:t]
    if t > 0
        s = copy(s)
        for i in t:-1:1
            if s[i] < ref[i + (n - t)]
                j = 1
                while ref[j] <= s[i]; j += 1; end
                s[i] = ref[j]
                for l in (i+1):t
                    s[l] = ref[j+=1]
                end
                changed = true
                break
            end
        end
        !changed && (s[1] = n+1)
    else
        s = [n+1]
    end
    (comb, s)
end
done(c::MultiSetCombinations, s) =
    (!isempty(s) && max(s[1], c.t) > length(c.ref)) ||  (isempty(s) && c.t > 0)

immutable WithReplacementCombinations{T}
    a::T
    t::Int
end

eltype{T}(::Type{WithReplacementCombinations{T}}) = Vector{eltype(T)}

length(c::WithReplacementCombinations) = binomial(length(c.a)+c.t-1, c.t)

"generate all combinations with replacement of size t from an array a."
with_replacement_combinations(a, t::Integer) = WithReplacementCombinations(a, t)

start(c::WithReplacementCombinations) = [1 for i in 1:c.t]
function next(c::WithReplacementCombinations, s)
    n = length(c.a)
    t = c.t
    comb = [c.a[si] for si in s]
    if t > 0
        s = copy(s)
        changed = false
        for i in t:-1:1
            if s[i] < n
                s[i] += 1
                for j in (i+1):t
                    s[j] = s[i]
                end
                changed = true
                break
            end
        end
        !changed && (s[1] = n+1)
    else
        s = [n+1]
    end
end
done(c::WithReplacementCombinations, s) = !isempty(s) && s[1] > length(c.a) || c.t < 0

function qkflat(A)
    result = Any[]
    grep(a) = for x in a
        isa(x,Array) ? grep(x) : push!(result,x)
    end
    grep(A)
result
end

immutable GlxAr{T}
    a::T
    t::Int
end

eltype{T}(::Type{GlxAr{T}}) = Vector{eltype(T)}

length(c::GlxAr) = binomial(length(c.a)+c.t-1, c.t)

"Generate a graded lex array of all combinations of a vector a[], that is, lex'd in steps per total degree of each row,but first a minor tweak on with_rep..."

pre_glex(a,t::Integer) = GlxAr(a,t)

start(c::GlxAr) = [1 for i in 1:c.t]
function next(c::GlxAr, s)
    n = length(c.a)
    t = c.t
    comb = [c.a[si] for si in s]
    if t > 0
        s = copy(s)
        changed = false
        for i in t:-1:1
            if s[i] < n
                s[i] += 1
                for j in (i+1):t
                    s[j] = s[i]
                end
                changed = true
                break
            end
        end
        !changed && (s[1] = n+1)
    else
        s = [n+1]
    end
    comb = qkflat((unique(permutations(comb)))) #Note depdcy's          
    (comb, s)
end

done(c::GlxAr, s) = !isempty(s) && s[1] > length(c.a) || c.t < 0



function glexer(p,m)
    D = p*m
    a = collect(0:1:p)
    G_0 = collect(pre_glex(a,m))
    G_0 = sortcols( reshape( vcat(G_0...),(m,Int(size(vcat(G_0...),1)/m))),rev=false)
    G = zeros(Int, m,1)
    for j = 1:D
        for i = 2:size(G_0,2)
            if sum(G_0[:,i]) !=j
                continue
            end
            G = hcat(G,G_0[:,i])                    
            if sum(G[:,end]) > p #
                return(G[:,1:end-1])                
            end
         end
    end
end

"""Multiply two input vectors with multivariate polynomial in/out"""
function multprod(p,m, U=ones(Int64,(1,p)), V=ones(Int64,(1,p)))
    G = glexer(p,m)
    r = size(G,2)
    if length(U) > r
        U = U[1:r]
    end
    if length(V) > r         
        V = V[1:r]
    end
    if length(U) < r || length(V) < r
        U = hcat(U,zeros(1,r-length(U)))
        V = hcat(V,zeros(1,r-length(V)))  
    end
    LU = length(U)
    LV = length(V)
    L = size(G,2)
    Dee = Any[]
    C = Any[]
    G = vcat(reshape(zeros(1,L),(1,L)),G)
    for i = 1:LU, j = 1:LV   #Emulating Matlab's "Prod"
        if U[i]*V[j] != 0
          push!(C,U[i]*V[j])
            for q = 1:m
                push!(Dee,(G[2:end,i]+G[2:end,j])[q])
            end
        end
    end
    g = Int(length(Dee)/m)
    Dee = reshape(Dee,(m,g))
    C = reshape(C,(1,g))
    Dee = vcat(C,Dee)
    
    for i = 1:L, j = 1:size(Dee,2)
#        if i>4 && sum(G[1,i-4:i])==0            
#            return(G)            
#        end        
        if G[2:end,i] != Dee[2:end,j]
            continue
        else
            G[1,i] = G[1,i]+Dee[1,j]
        end
    end    
    return(G) #only needed as a failsafe for low-order terms
end
