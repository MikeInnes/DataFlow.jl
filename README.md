# DataFlow.jl

[![Build Status](https://travis-ci.org/MikeInnes/DataFlow.jl.svg?branch=master)](https://travis-ci.org/MikeInnes/DataFlow.jl)

DataFlow.jl is a bit like [MacroTools](https://github.com/MikeInnes/MacroTools.jl), but instead of working with programs as expression trees, it works with them as dataflow graphs.

A data flow graph is a bit like an expression tree without variables; functions always refer to their inputs directly. Underneath it's a directed graph linking the output of one function call to the input of another. DataFlow.jl provides functions like `prewalk` and `postwalk` which allow you to do crazy graph-restructuring operations with minimal code, *even on cyclic graphs*. Think algorithms like common subexpression elimination implemented in [one line](https://github.com/MikeInnes/DataFlow.jl/blob/d5899a47ed052190e655afdf1510e021ad95d09d/src/operations.jl#L2) rather than hundreds.

DataFlow.jl also provides a common syntax for representing dataflow graphs. This can be used by other packages (like [Flux](https://github.com/MikeInnes/Flux.jl)) to provide a common, intuitive way to work with embedded graphical DSLs. This approach could be applied to an extremely wide range of domains, like graphical modelling in statistics and machine learning, parallel  and distributed computing or hardware modelling and simulation.

## Basic Examples

Consider a simple function for calculating variance:

```julia
@flow function var(xs)
  mean = sum(xs)/length(xs)
  meansqr = sumabs2(xs)/length(xs)
  meansqr - mean^2
end
```

This looks like (and is) perfectly valid Julia code, but the `@flow` annotation out front makes a big difference; instead of being stored internally as an AST, the code is stored as a directed graph like this:

![](static/variance.png)

The variables are stripped out and we directly model how data moves between different operation. Notice that, for one thing, this makes opportunities for parallelism structurally obvious.

We can run common subexpression elimination on the graph as follows:

```julia
julia> DataFlow.cse(var.output)
DataFlow.IVertex{Any}
chamois = length(xs)
sumabs2(xs) / chamois - (sum(xs) / chamois) ^ 2
```

Multiple things have happened to transform our original code. `mean` and `meansqr` did not need to be assigned variables, so they weren't. Conversely, `length(xs)` *is* assigned a variable name because the result is used more than once. Another thing you can try is modifying `var` to contain an unused variable, and noticing that it gets stripped out. This seems like a very complex syntax operation, but `cse` is implemented in only a couple of lines.

Another unusual feature of DataFlow is that it supports cycles, for example:

```julia
@flow function recurrent(x)
  hidden = σ( Wxh*x + Whh*hidden )
  y = σ( Why*hidden + Wxy*x )
end
```

This is not valid Julia, since `hidden` must be defined before it is used. In DataFlow.jl this is simply represented as a graph like the following:

![](static/recurrent.png)

Applications that build on DataFlow.jl can decide what meaning to give to structures like this. For example, an ANN library might unroll the network a given number of steps at a cycle, enabling recurrent neural network architectures to be easily expressed.
