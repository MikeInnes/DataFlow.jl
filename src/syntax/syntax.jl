import Base: @get!

include("read.jl")
include("dump.jl")
include("sugar.jl")

# Display

syntax(v::Vertex) = syntax(dl(v))

function Base.show(io::IO, v::Vertex)
  print(io, typeof(v))
  print(io, "(")
  s = MacroTools.alias_gensyms(syntax(v))
  if length(s.args) == 1
    print(io, sprint(print, s.args[1]))
  else
    foreach(x -> (println(io); print(io, sprint(print, x))), s.args)
  end
  print(io, ")")
end

import Juno: Row, Tree

code(x) = Juno.Model(Dict(:type=>"code",:text=>x,:attrs=>Dict(:block=>true)))

@render Juno.Inline v::Vertex begin
  s = MacroTools.alias_gensyms(syntax(v))
  Juno.LazyTree(typeof(v), () -> map(s -> code(string(s)), s.args))
end

# Function / expression macros

export @flow, @iflow, @vtx, @ivtx

function flow_func(ex)
  @capture(shortdef(ex), name_(args__) = exs__)
  @assert all(isa.(args, Symbol))
  output = graphm(exs, args = args)
  :($(esc(name)) = $output)
end

function flowm(ex, f = dl)
  isdef(ex) && return flow_func(ex)
  g = graphm(block(ex))
  g = mapconst(x -> isexpr(x, :$) ? esc(x.args[1]) : Expr(:quote, x), g)
  constructor(f(g))
end

macro flow(ex)
  flowm(ex)
end

macro iflow(ex)
  flowm(ex, il)
end

macro vtx(ex)
  exs = il(graphm(block(ex)))
  exs = prewalkλ(withconst(esc), exs)
  return constructor(exs)
end
