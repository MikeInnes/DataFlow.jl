using DataFlow, DataFlow.Fuzz
using MacroTools, Lazy, Base.Test

import DataFlow: Call, graphm, syntax, dvertex, constant, prewalk

@testset "DataFlow" begin

@testset "I/O" begin

for nodes = 1:10, tries = 1:100

  dl = grow(DVertex, nodes)

  @test dl == graphm(Dict(), syntax(dl))

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

@test @capture syntax(recurrent) begin
  h_Symbol = σ( Wxh*xs_ + Whh*h_Symbol + bh )
  σ( Wxy*x + Why*h_Symbol + by )
end

@flow function var(xs)
  mean = sum(xs_)/length(xs_)
  meansqr = sumabs2(xs_)/length(xs_)
  meansqr - mean^2
end

@test @capture syntax(var) begin
  sumabs2(xs_)/length(xs_) - (sum(xs_) / length(xs_)) ^ 2
end

let x = :(2+2)
  @test @flow(foo($x)) == dvertex(Call(), constant(:foo), constant(x))
end

end

end
