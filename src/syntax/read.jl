# Syntax → Graph

struct LateVertex{T}
  val::DVertex{T}
  args::Vector{Any}
end

function bindings(ex)
  bs = []
  for ex in ex.args
    @capture(ex, x_ = _) && push!(bs, x)
  end
  return bs
end

function normedges(ex)
  map!(ex.args, ex.args) do ex
    isline(ex) ? ex :
    @capture(ex, _ = _) ? ex :
    :($(gensym("edge")) = $ex)
  end
  return ex
end

normalise(ex) =
  @> ex normsplits normclosures normedges normlines desugar

function latenodes(exs)
  bindings = d()
  for ex in exs
    @capture(ex, b_Symbol = (f_(a__) | f_)) || error("invalid flow binding `$ex`")
    bindings[b] = a == nothing ? constant(f) : LateVertex(dvertex(f), a)
  end
  return bindings
end

graphm(bindings, node) = constant(node)
graphm(bindings, node::Vertex) = node
graphm(bindings, ex::Symbol) =
  haskey(bindings, ex) ? graphm(bindings, bindings[ex]) : constant(ex)
graphm(bindings, node::LateVertex) = node.val

function graphm(bindings, ex::Expr)
  isexpr(ex, :block) && return graphm(bindings, ex.args)
  @capture(ex, f_(args__)) || return constant(ex)
  dvertex(f, map(ex -> graphm(bindings, ex), args)...)
end

function fillnodes!(bindings)
  for (b, node) in bindings
    if isa(node, Vertex) && isconstant(node) && haskey(bindings, value(node).value)
      alias = bindings[value(node).value]
      isa(alias, LateVertex) && (alias = alias.val)
      bindings[b] = alias
    end
  end
  for (b, node) in bindings
    isa(node, LateVertex) || continue
    for arg in node.args
      thread!(node.val, graphm(bindings, arg))
    end
    bindings[b] = node.val
  end
  return bindings
end

function graphm(bindings, exs::Vector)
  exs = normalise(:($(exs...);)).args
  @capture(exs[end], result_Symbol = _)
  merge!(bindings, latenodes(exs))
  fillnodes!(bindings)
  output = graphm(bindings, result)
end

graphm(x) = graphm(d(), x)
