cse(v::IVertex, cache = Dict{typeof(v),typeof(v)}()) =
  postwalk(x -> get!(cache, x, x), v)

cse(v::Vertex, cache = d()) = cse(il(v), cache)

function cse(vs::Vector)
  cache = d()
  [cse(v, cache) for v in vs]
end

function duplicates(v::IVertex)
  cache = Dict{typeof(v),Int}()
  prewalk(v) do v
    cache[v] = get!(cache, v, 0) + 1
    v
  end
  cache = filter((_,n) -> n > 1, cache)
  cache = filter((v,_) -> !any(v′ -> v′ ≠ v && contains_(v′, v), keys(cache)), cache)
end

function contains_(haystack::IVertex, needle::IVertex)
  result = false
  prewalk(haystack) do v
    result |= v == needle
    v
  end
  return result
end

contains_(v::Vertex, w::Vertex) = contains_(il(v), il(w))

function common(v::IVertex, w::IVertex, seen = OSet())
  w in seen && return Set{typeof(w)}()
  push!(seen, w)
  if contains_(v, w)
    Set{typeof(w)}((w,))
  else
    union((common(v, w′, seen) for w′ in inputs(w))...)
  end
end

common(v::Vertex, w::Vertex) = common(il(v), il(w))
