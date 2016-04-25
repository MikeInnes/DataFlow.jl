type Identity end

function inputsm(args)
  graph = Vertex{Any}(Identity())
  bindings = d()
  for (i, arg) in enumerate(args)
    isa(arg, Symbol) || error("invalid argument $arg")
    bindings[arg] = Needle(graph, i)
  end
  return graph, bindings
end

type LateVertex{T}
  val::Vertex{T}
  args::Vector{Any}
end

function latenodes(exs)
  bindings = d()
  for ex in exs
    @capture(ex, b_Symbol = f_(a__)) || error("invalid flow binding `$ex`")
    bindings[b] = LateVertex(Vertex{Any}(f), a)
  end
  return bindings
end

graphm(bindings, node) = Vertex{Any}(node)
graphm(bindings, ex::Symbol) =
  haskey(bindings, ex) ?
    graphm(bindings, bindings[ex]) :
    Vertex{Any}(ex)
graphm(bindings, node::Vertex) = node
graphm(bindings, node::Needle) = node
graphm(bindings, node::LateVertex) = node.val

function graphm(bindings, ex::Expr)
  @capture(ex, f_(args__)) || error("invalid flow expression `$ex`")
  Vertex{Any}(f, map(ex -> graphm(bindings, ex), args)...)
end

function extractresult!(args)
  @match args[end] begin
    (return a_) => (args[end] = a; extractresult!(args))
    (out_ = _) => out
    _ => pop!(args)
  end
end

function fillnodes!(bindings)
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
  result = extractresult!(exs)
  merge!(bindings, latenodes(exs))
  fillnodes!(bindings)
  output = graphm(bindings, result)
end

graphm(x) = graphm(d(), x)

type SyntaxGraph
  args::Vector{Symbol}
  input::Vertex{Any}
  output::Vertex{Any}
end

function flow_func(ex)
  @capture(shortdef(ex), name_(args__) = exs__)
  input, bs = inputsm(args)
  output = graphm(bs, exs)
  :($(esc(name)) = $(SyntaxGraph(args, input, output)))
end

# TODO: islands

function constructor!(v::Vertex, ex, bindings = d())
  haskey(bindings, v) && return bindings[v]
  is = [constructor!(v, ex, bindings) for v in inputs(v)]
  if length(outputs(v)) > 1 # FIXME
    @gensym vertex
    bindings[v] = vertex
    v < v ?
      push!(ex.args, :($vertex = Vertex($(v.value))), :(thread!($vertex, $(is...)))) :
      push!(ex.args, :($vertex = Vertex($(v.value), $(is...))))
    return v
  else
    return :(Vertex($(v.value), $(is...)))
  end
end

constructor!(v::Needle, ex, bs = d()) =
  constructor!(v.vertex, ex, bs) # FIXME

function constructor(outs)
  ex, bs = :(;), d()
  for v in outs
    push!(ex.args, constructor!(v, ex, bs))
  end
  return ex
end

macro flow(ex)
  isdef(ex) && return flow_func(ex)
  @capture(ex, exs__)
  graph = graphm(exs)
end
