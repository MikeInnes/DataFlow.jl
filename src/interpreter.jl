mux(f) = f
mux(m, f) = (xs...) -> m(f, xs...)
mux(ms...) = foldr(mux, ms)

type Context{T}
  interp::T
  cache::ObjectIdDict
  stack::Vector{Any}
  data::Dict{Symbol,Any}
end

Context(interp; kws...) = Context(interp, ObjectIdDict(), [], Dict{Symbol,Any}(kws))

Base.getindex(ctx::Context, k::Symbol) = ctx.data[k]
Base.setindex!(ctx::Context, v, k::Symbol) = ctx.data[k] = v

function stack(c::Context)
  stk = []
  isempty(c.stack) && return stk
  frame = nothing
  for i = 1:length(c.stack)
    isa(c.stack[i], Frame) || continue
    i > 1 && isa(c.stack[i-1], Line) && unshift!(stk, (frame, c.stack[i-1]))
    frame = c.stack[i].f
  end
  isa(c.stack[end], Line) && unshift!(stk, (frame, c.stack[end]))
  return stk
end

function interpv(ctx::Context, graph::IVertex)
  haskey(ctx.cache, graph) && return ctx.cache[graph]
  ctx.cache[graph] = ctx.interp(ctx, value(graph), inputs(graph)...)
end

interpv(ctx::Context, xs::Tuple) = map(x -> interpv(ctx, x), xs)

function interpret(ctx::Context, graph::IVertex, args::IVertex...)
  graph = spliceinputs(graph, args...)
  interpv(ctx, graph)
end

interpret(ctx::Context, graph::IVertex, args...) =
  interpret(ctx, graph, map(constant, args)...)

# The `ifoo` convention denotes a piece of interpreter middleware

iconst(f, ctx::Context, x::Constant) = x.value

function iline(f, ctx::Context, l::Union{Line,Frame}, v)
  push!(ctx.stack, l)
  val = interpv(ctx, v)
  pop!(ctx.stack)
  return val
end

ilinev(f, ctx::Context, l::Union{Line,Frame}, v) = vertex(l, iline(f, ctx, l, v))

ilambda(f, ctx::Context, ::Flosure, body, vars...) =
  (xs...) -> interpret(ctx, flopen(body), vars..., xs...)

iargs(cb, ctx::Context, f, xs...) = cb(ctx, f, interpv(ctx, xs)...)

function ituple(f, ctx::Context, s::Split, xs)
  isa(xs, Vertex) && value(xs) == tuple ? inputs(xs)[s.n] :
  isa(xs, Tuple) ? xs[s.n] :
    f(s, xs)
end

for m in :[iconst, iline, ilinev, ilambda, ituple].args
  @eval $m(f, args...) = f(args...)
end

interpeval = mux(iline, ilambda, iconst, iargs,
                 ituple, (ctx, f, xs...) -> f(xs...))

interpret(graph::IVertex, args...) =
  interpret(Context(interpeval), graph, args...)

# Error Handling

import Juno: errmsg, errtrace

framename(f::Function) = typeof(f).name.mt.name
framename(f::Void) = Symbol("<none>")
framename(x) = symbol(string(typeof(x)))

totrace(stack) = [StackFrame(framename(f), Symbol(line.file), line.line)
                  for (f, line) in stack]

type Exception{T}
  err::T
  trace::StackTrace
end

errmsg(e::Exception) = errmsg(e.err)
errtrace(e::Exception, bt) = errtrace(e.err, [e.trace..., bt...])
