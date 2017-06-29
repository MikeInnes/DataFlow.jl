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

function normreturn(ex)
  @capture(ex.args[end], return x_) && (ex.args[end] = x)
  ex
end

function normedges(ex)
  ex = normreturn(ex)
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

function fillnodes!(bindings, nodes)
  # TODO: remove this once constants are fixed
  for b in nodes
    node = bindings[b]
    if isa(node, Vertex) && isconstant(node) && haskey(bindings, value(node[1]))
      alias = bindings[value(node[1])]
      isa(alias, LateVertex) && (alias = alias.val)
      bindings[b] = alias
    end
  end
  for b in nodes
    node = bindings[b]
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
  lates = latenodes(exs)
  merge!(bindings, lates)
  fillnodes!(bindings, keys(lates))
  output = graphm(bindings, result)
end

graphm(x) = graphm(d(), block(x))
