using DataFlow, DataFlow.Fuzz
using MacroTools, Lazy, Base.Test

import DataFlow: graphm, syntax, cse, dvertex, constant, prewalk

@testset "DataFlow" begin

@testset "I/O" begin

for nodes = 1:10, tries = 1:100

  dl = grow(DVertex, nodes)

  @test dl == @> dl syntax(bindconst = true) graphm

  @test copy(dl) == dl

  il = grow(IVertex, nodes)

  @test il == @> il DataFlow.dl() DataFlow.il()

  @test copy(il) == il == prewalk(identity, il)

end

end

@testset "Syntax" begin

@flow function recurrent(xs)
  hidden = σ( Wxh*xs + Whh*hidden + bh )
  σ( Wxy*x + Why*hidden + by )
end

@test @capture syntax(recurrent.output) begin
  h_Symbol = σ( Wxh*xs + Whh*h_Symbol + bh )
  σ( Wxy*x + Why*h_Symbol + by )
end

@flow function var(xs)
  mean = sum(xs)/length(xs)
  meansqr = sumabs2(xs)/length(xs)
  meansqr - mean^2
end

@test @capture syntax(var.output) begin
  sumabs2(xs)/length(xs) - (sum(xs) / length(xs)) ^ 2
end

@test contains(sprint(show, var),
               string(:(sumabs2(xs)/length(xs) - (sum(xs) / length(xs)) ^ 2)))

@test cse(var.output) == convert(IVertex, @flow begin
  n = length(xs)
  sumabs2(xs)/n - (sum(xs) / n) ^ 2
end)

let x = :(2+2)
  @test @flow(foo($x)) == dvertex(:foo, constant(x))
end

end

end
