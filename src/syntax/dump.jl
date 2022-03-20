# Graph → Syntax

toexpr(f, xs...) = :($f($(xs...)))

binding(bindings::AbstractDict, v) =
  haskey(bindings, v) ? bindings[v] : (bindings[v] = gensym("edge"))

function syntax(head::DVertex; bindconst = !isfinal(head))
  vs = topo(head)
  ex, bs = @q(begin end), IdDict{Any ,Any}()
  for v in vs
    x = toexpr(value(v), [binding(bs, n) for n in inputs(v)]...)
    if !bindconst && isconstant(v) && nout(v) > 1
      bs[v] = v.value.value
    elseif nout(v) > 1 || (!isfinal(head) && v ≡ head)
      edge = binding(bs, v)
      push!(ex.args, :($edge = $x))
    elseif haskey(bs, v)
      if MacroTools.inexpr(ex, bs[v])
        ex = MacroTools.replace(ex, bs[v], x)
      else
        push!(ex.args, :($(bs[v]) = $x))
      end
    else
      isfinal(v) ? push!(ex.args, x) : (bs[v] = x)
    end
  end
  head ≢ vs[end] && push!(ex.args, binding(bs, head))
  return ex
end

# TODO: this is butt ugly

function constructor(g)
  vertex = isa(g, DVertex) ? :(DataFlow.dvertex) : :(DataFlow.vertex)
  g = mapv(g) do v
    value(v) isa Lambda && (v.value = :(DataFlow.Lambda($(value(v).args), $(constructor(value(v).body)))))
    value(v) isa Constant && (v.value = :(DataFlow.Constant($(value(v).value))))
    prethread!(v, typeof(v)(Constant(value(v))))
    prethread!(v, typeof(v)(Constant(vertex)))
    v.value = Call()
    v
  end
  ex = syntax(g)
  decls, exs = [], []
  for x in block(ex).args
    if @capture(x, v_ = $vertex(f_, a__))
      push!(decls, :($v = $vertex($f)))
      push!(exs, :(DataFlow.thread!($v, $(a...))))
    else
      push!(exs, x)
    end
  end
  return @q begin
    $(decls...)
    $(exs...)
  end
end
