mutable struct DVertex{T} <: Vertex{T}
  value::T
  inputs::Vector{DVertex{T}}
  outputs::OASet{DVertex{T}}

  DVertex{T}(x) where T = new(x, [], OASet{DVertex{T}}())
end

DVertex(x) = DVertex{typeof(x)}(x)

value(v::DVertex) = v.value
inputs(v::DVertex) = v.inputs
outputs(v::DVertex) = v.outputs

function thread!(to::DVertex, from::DVertex)
  push!(inputs(to), from)
  push!(outputs(from), to)
  return to
end

function prethread!(to::DVertex, from::DVertex)
  unshift!(inputs(to), from)
  push!(outputs(from), to)
  return to
end

dvertex(a...) = DVertex{Any}(a...)

dvertex(x::Vertex) = convert(DVertex{Any}, x)

dl(v::Vertex) = convert(DVertex, v)

nin(v::Vertex) = length(inputs(v))

function nout(v::Vertex)
  n = 0
  for o in outputs(v), i in inputs(o)
    i ≡ v && (n += 1)
  end
  return n
end

isfinal(v::Vertex) = nout(v) == 0

function equal(a::Vertex, b::Vertex, seen = OSet())
  (a, b) ∈ seen && return true
  (value(a) == value(b) &&
    length(inputs(a)) == length(inputs(b)) &&
    length(outputs(a)) == length(outputs(b))) || return false
  push!(seen, (a, b))
  for (i, j) in zip(inputs(a), inputs(b))
    equal(i, j, seen) || return false
  end
  @assert @>> a outputs map(value) allunique
  @assert @>> b outputs map(value) allunique
  for o in outputs(a)
    p = filter(p -> value(p) == value(o), collect(outputs(b)))
    isempty(p) && return false
    equal(o, first(p), seen) || return false
  end
  return true
end

import Base: ==

x::Vertex == y::Vertex = equal(x, y)

function mapv(f, v::Vertex; cache = ODict())
  haskey(cache, v) && return cache[v]
  node = cache[v] = typeof(v)(value(v))
  for out in outputs(v)
    push!(node.outputs, mapv(f, out, cache = cache))
  end
  for in in inputs(v)
    push!(node.inputs, mapv(f, in, cache = cache))
  end
  return f(node)
end

Base.map(f, v::DVertex) = mapv(v -> (v.value = f(v.value); v), v)

copy(v::DVertex) = mapv(identity, v)
