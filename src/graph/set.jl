const ASet{T} = Base.AbstractSet{T}
const ODict = IdDict

struct ObjectIdSet{T} <: ASet{T}
  dict::IdDict{Any, Any}
  ObjectIdSet{T}() where T = new(IdDict{Any, Any}())
end

Base.eltype(::ObjectIdSet{T}) where T= T

ObjectIdSet() = ObjectIdSet{Any}()

Base.push!(s::ObjectIdSet{T}, x::T) where T= (s.dict[x] = nothing; s)
Base.delete!(s::ObjectIdSet{T}, x::T) where T= (delete!(s.dict, x); s)
Base.in(x, s::ObjectIdSet) = haskey(s.dict, x)

(::Type{ObjectIdSet{T}})(xs) where T= push!(ObjectIdSet{T}(), xs...)

ObjectIdSet(xs) = ObjectIdSet{eltype(xs)}(xs)

Base.collect(s::ObjectIdSet) = collect(keys(s.dict))
Base.similar(s::ObjectIdSet, T::Type) = ObjectIdSet{T}()

@forward ObjectIdSet.dict Base.length

@iter xs::ObjectIdSet -> keys(xs.dict)

const OSet = ObjectIdSet

struct ObjectArraySet{T} <: ASet{T}
  xs::Vector{T}
  ObjectArraySet{T}() where T = new(T[])
end

Base.in(x::T, s::ObjectArraySet{T}) where T= any(y -> x ≡ y, s.xs)
Base.push!(s::ObjectArraySet, x) = (x ∉ s && push!(s.xs, x); s)

function Base.delete!(s::ObjectArraySet, x)
  i = findfirst(s.xs, x)
  i ≠ 0 && deleteat!(s.xs, i)
  return s
end

(::Type{ObjectArraySet{T}})(xs) where T= push!(ObjectArraySet{T}(), xs...)

ObjectArraySet(xs) = ObjectArraySet{eltype(xs)}(xs)

Base.collect(xs::ObjectArraySet) = xs.xs
Base.similar(s::ObjectArraySet, T::Type) = ObjectArraySet{T}()

@forward ObjectArraySet.xs Base.length

@forward ObjectArraySet.xs Base.iterate

const OASet{T} = ObjectArraySet{T}
