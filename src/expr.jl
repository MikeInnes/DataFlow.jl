toexpr(s::Symbol) = s

function toexpr(bindings, v::Vertex)
  haskey(bindings, v) && return bindings[v]
  isa(value(v), Constant) && return value(v).value
  return Expr(:call, value(v), map(v -> toexpr(bindings, v), v.inputs)...)
end

# TODO: support multiple outputs
toexpr(bindings, v::Needle) = get(bindings, v, toexpr(bindings, v.vertex))

function toexpr(g::SyntaxGraph)
  iscyclic(g.input) && return :(error("Can't execute cyclic graph"))
  bindings = d()
  for (i, arg) in enumerate(g.args)
    bindings[Needle(g.input, i)] = arg
  end
  exs = []
  # TODO: dependency awareness
  # Should be easy, just treat the nodes as partially ordered by `isreaching`
  # and sort them
  reaching(g.input) do v
    length(outputs(v)) > 1 || return
    name = gensym()
    bindings[Needle(v, 1)] = name
    push!(exs, :($name = $(toexpr(bindings, v))))
  end
  push!(exs, toexpr(bindings, g.output))
  return :($(exs...);)
end

function toexpr(g::SyntaxGraph, args...)
  length(args) == length(g.args) || error("Wrong number of arguments")
  :(let $([:($(g.args[i]) = $(args[i])) for i = 1:length(args)]...)
      $(toexpr(g))
    end) |> eval
end
