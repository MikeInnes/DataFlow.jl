using DataFlow, DataFlow.Fuzz
using MacroTools, Lazy, Test

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

var = @flow begin
  mean = sum(xs)/length(xs)
  meansqr = sumabs2(xs)/length(xs)
  meansqr - mean^2
end

@test @capture syntax(DataFlow.striplines(var)) begin
  sumabs2(xs)/length(xs) - (sum(xs) / length(xs)) ^ 2
end

let x = :(2+2)
  @test @flow(foo($x)) == vertex(Call(), constant(:foo), constant(x))
end

end

end
