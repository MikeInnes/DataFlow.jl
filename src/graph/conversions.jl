import Base: convert

for (V, W) in [(DVertex, IVertex), (IVertex, DVertex)]
  @eval function convert(::Type{$W{T}}, v::$V, cache = ODict()) where T
    haskey(cache, v) && return cache[v]
    w = cache[v] = $W{T}(value(v))
    thread!(w, [convert($W{T}, v′, cache) for v′ in inputs(v)]...)
  end
  @eval convert(::Type{$W}, v::Vertex) = convert($W{eltype(v)}, v)
end
