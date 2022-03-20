__precompile__()

module DataFlow

using MacroTools, Juno, Lazy
using Base.Iterators: filter
using MacroTools: @q, @forward

include("graph/graph.jl")
include("syntax/syntax.jl")
include("operations.jl")
include("interpreter.jl")
include("fuzz.jl")

end # module
