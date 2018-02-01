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

export @flow, @vtx

macro flow(ex)
  v = il(graphm(block(ex)))
  v = prewalkλ(withconst(x -> isexpr(x, :$) ? esc(x.args[1]) : Expr(:quote, x)), v)
  constructor(v)
end

macro vtx(ex)
  v = il(graphm(block(ex)))
  v = prewalkλ(withconst(esc), v)
  return constructor(v)
end
