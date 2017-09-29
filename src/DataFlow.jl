__precompile__()

module DataFlow

using Lazy, MacroTools, Juno
using Base.Iterators: filter

include("graph/graph.jl")
include("syntax/syntax.jl")
include("operations.jl")
include("interpreter.jl")
include("fuzz.jl")

end # module
