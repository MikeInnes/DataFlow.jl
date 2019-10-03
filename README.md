# DataFlow.jl

[![Build Status](https://travis-ci.org/MikeInnes/DataFlow.jl.svg?branch=master)](https://travis-ci.org/MikeInnes/DataFlow.jl)

**Note:** This package is deprecated. You should take a look at [IRTools](https://github.com/MikeInnes/IRTools.jl) instead.

DataFlow.jl is a code intermediate representation (IR) format, representing code as an expression graph. It supports closures are represented explicitly, allowing full programs to be easily represented and manipulated and complex whole-program transformations to be applied. Moreover, programs can be kept in a high-level form that's very human-readable.

A data flow graph is a bit like an expression tree without variables; functions always refer to their inputs directly. Underneath it's a directed graph linking the output of one function call to the input of another. DataFlow.jl provides functions like `prewalk` and `postwalk` which allow you to do crazy graph-restructuring operations with minimal code, *even on cyclic graphs*. Think algorithms like common subexpression elimination implemented in [one line](https://github.com/MikeInnes/DataFlow.jl/blob/d5899a47ed052190e655afdf1510e021ad95d09d/src/operations.jl#L2) rather than hundreds.

## Basics

```julia
julia> using DataFlow: vertex, constant, Call
```

DataFlow.jl provides the `IVertex` data type, which behaves a lot like Julia's `Expr` type. We can construct vertices, and use them as inputs to other vertices, to build expressions. `constant` is a shortcut for vertices representing constant values.

```julia
julia> using DataFlow: vertex, constant, Call, Constant

julia> a, b = constant(1), constant(2)
(IVertex(1), IVertex(2))

julia> c = vertex(Call(), constant(+), a, b)
IVertex((+)(1, 2))
```

The `Call()` object is analagous to the "head" in Julia's `Expr`s, so this is like `Expr(:call, f, x...)`.

A key difference from `Expr` is that the `IVertex` is a graph, not a tree, and reuse is explicitly represented. Consider multiplying the expression `c` by itself:

```julia
julia> d = vertex(Call(), constant(*), c, c)
IVertex(
bison = (+)(1, 2)
(*)(bison, bison))
```

In order to represent the structure of the graph in text, DataFlow.jl prints an expression tree with a made-up variable binding (`bison`). This variable is _not_ present in the graph itself, but just used for presentation.

Graphs can also be dumped to Julia expressions using `DataFlow.syntax`, which will similarly create variable bindings where needed.

```julia
julia> DataFlow.syntax(d)
quote
    ##edge#668 = (+)(1, 2)
    (*)(##edge#668, ##edge#668)
end

julia> eval(ans)
9
```

Graphs are also allowed to be cyclic. We can introduce cycles using `thread!`, which pushes a new argument into an existing vertex.

```julia
julia> DataFlow.thread!(c, c)
IVertex(bison = (+)(1, 2, bison))
```

Notice that the cycle is represented by the circular dependency of `bison` on itself.

## Walking

Transformations are carried out via `prewalk` and `postwalk` functions very similar to those in [MacroTools](https://github.com/MikeInnes/MacroTools.jl) (see there for more explanation).

```julia
julia> DataFlow.prewalk(d) do v
         v.value isa Call && v[1].value == Constant(+) ? vertex(constant(-), v[2:end]...) : v
       end
IVertex(
bison = (IVertex(-))(1, 2)
(*)(bison, bison))
```

There are also in-place variants of prewalk and postwalk, which can be used for more advanced transformations.
