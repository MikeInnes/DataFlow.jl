mutable struct IVertex{T} <: Vertex{T}
  value::T
  inputs::Vector{IVertex{T}}

  IVertex{T}(x) where T = new(x, [])
end

IVertex(x) = IVertex{typeof(x)}(x)

value(v::IVertex) = v.value
inputs(v::IVertex) = v.inputs
outputs(v::IVertex) = ()
nout(v::IVertex) = 0

function thread!(to::IVertex, from::IVertex)
  push!(inputs(to), from)
  return to
end

function prethread!(to::IVertex, from::IVertex)
  unshift!(inputs(to), from)
  return to
end

il(v::Vertex) = convert(IVertex, v)

vertex(a...) = IVertex{Any}(a...)

vertex(x::Vertex) = convert(IVertex{Any}, x)

struct Stop
  x
end

stop(x) = Stop(x)

unwrap_stop(x) = false, x
unwrap_stop(x::Stop) = true, x.x

function walk!(v::IVertex, pre, post, cache = ODict())
  haskey(cache, v) && return cache[v]::typeof(v)
  stop, v′ = unwrap_stop(pre(v))
  cache[v] = v′
  stop || map!(v -> walk!(v, pre, post, cache), v′.inputs, v′.inputs)
  cache[v] = post(v′)
end

prewalk!(f, v::IVertex) = walk!(v, f, identity)
postwalk!(f, v::IVertex) = walk!(v, identity, f)

copy1(v::IVertex) = typeof(v)(v.value, v.inputs...)

precopy(v) = copy1(v)
precopy(v::Stop) = Stop(v.x)

walk(v::IVertex, pre, post) = walk!(v, v -> precopy(pre(v)), post)

prewalk(f, v::IVertex) = walk(v, f, identity)
postwalk(f, v::IVertex) = walk(v, identity, f)

copy(v::IVertex) = walk(v, identity, identity)

Base.map(f, v::IVertex) = prewalk(v -> typeof(v)(f(value(v)), inputs(v)...), v)

Base.replace(v::IVertex, pat, r) = prewalk(v -> v == pat ? r : v, v)

prefor(f, v) = prewalk!(v -> (f(v); v), v)

# TODO: check we don't get equivalent hashes for different graphs

function hash(v::IVertex, h::UInt = UInt(0), seen = OSet())
  h = hash(value(v), h)
  v in seen ? (return h) : push!(seen, v)
  for n in inputs(v)
    h ⊻= hash(n, h, seen)
  end
  return h
end

function iscyclic(v::IVertex)
  is = false
  prefor(v -> is |= ↺(v), v)
  return is
end

function Base.contains(haystack::IVertex, needle)
  result = false
  map(v -> result |= v == needle, haystack)
  return result
end
