import Base: ==

# Basic julia sugar

function normops(ex)
  MacroTools.prewalk(ex) do ex
    @match ex begin
      x_ .+ y_ => :((+).($x,$y))
      x_ .- y_ => :((-).($x,$y))
      x_ .* y_ => :((*).($x,$y))
      x_ ./ y_ => :((/).($x,$y))
      _ => ex
    end
  end
end

function desugar(ex)
  ex = normops(ex)
  MacroTools.prewalk(ex) do ex
    @match ex begin
      (xs__,)   => :($tuple($(xs...)))
      xs_[i__]  => :($getindex($xs, $(i...)))
      f_.(xs__) => :($broadcast($f, $(xs...)))
      _ => ex
    end
  end
end

tocall(::typeof(tuple), xs...) = :($(xs...),)
tocall(::typeof(getindex), x, i...) = :($x[$(i...)])
tocall(::typeof(broadcast), f, xs...) = :($f.($(xs...)))

# Constants

struct Constant end

tocall(c::Constant, x) = x.args[1]

isconstant(v::Vertex) = isa(value(v), Constant)

constant(x) = vertex(Constant(), vertex(x))
constant(v::Vertex) = vertex(v)

# Blocks

struct Do end

tocall(::Do, a...) = :($(a...);)

# Line Numbers

struct Line
  file::String
  line::Int
end

const noline = Line("", -1)

function Line(ex::Expr)
  @assert ex.head == :line
  Line(string(ex.args[2]), ex.args[1])
end

function normlines(ex)
  line = noline
  ex′ = :(;)
  for ex in ex.args
    isline(ex) && (line = Line(ex); continue)
    line == noline && (push!(ex′.args, ex); continue)
    @assert @capture(ex, var_ = val_)
    push!(ex′.args, :($var = $line($val)))
  end
  return ex′
end

function applylines(ex)
  ex′ = :(;)
  for ex in ex.args
    @capture(ex, (var_ = val_) | val_)
    val = MacroTools.postwalk(val) do ex
      @capture(ex, l_Frame(x_)) && return x # Ignore frames for now
      @capture(ex, l_Line(x_)) || return ex
      push!(ex′.args, Expr(:line, l.line, Symbol(l.file)))
      @gensym edge
      push!(ex′.args, :($edge = $x))
      return edge
    end
    isexpr(val, Symbol) ? (ex′.args[end].args[1] = val) :
      push!(ex′.args, var == nothing ? val : :($var = $val))
  end
  return ex′
end

struct Frame{T}
  f::T
end

struct SkipFrame end

function striplines(v)
  postwalk(v) do v
    isa(value(v), Line) || isa(value(v), Frame) ? v[1] : v
  end
end

# Static tuples

# TODO: just use `getindex` and `tuple` to represent these?
struct Split
  n::Int
end

# TODO: printing
function normsplits(ex)
  MacroTools.prewalk(ex) do ex
    @capture(ex, (xs__,) = y_) || return ex
    @gensym edge
    :($edge = $y;
      $((:($(xs[i]) = $(Split(i))($edge)) for i = 1:length(xs))...))
  end |> MacroTools.flatten |> block
end

tocall(s::Split, x) = :($x[$(s.n)])

group(xs...) = vertex(tuple, xs...)

# TODO: fail gracefully when tuples are short
function detuple(v::IVertex)
  postwalk(v) do v
    if isa(value(v), Split) && value(v[1]) == tuple
      v[1][value(v).n]
    else
      v
    end
  end
end

# Bindings

struct Bind
  name::Symbol
end

# TODO: printing
function insertbinds(ex)
  ls = map(ex.args) do l
    @capture(l, x_ = y_) || return l
    :($x = $(Bind(x))($y))
  end
  :($(ls...);)
end

# Inputs

struct Input end

inputnode(is...) = foldl((x, i) -> vertex(Split(i), x), constant(Input()), is)

isinput(v::IVertex) = isa(value(v), Split) && isconstant(v[1]) && value(v[1][1]) == Input()

function inputidx(v::IVertex)
  i = Int[]
  while value(v) isa Split
    unshift!(i, value(v).n)
    v = v[1]
  end
  v == constant(Input()) ? i : nothing
end

function bumpinputs(v::IVertex)
  prewalk(v) do v
    isinput(v) ?
      inputnode(value(v).n + 1) :
      v
  end
end

function spliceinput(v::IVertex, input::IVertex)
  postwalk(v) do v
    isconstant(v) && value(v[1]) == Input() ? input : v
  end
end

spliceinputs(v::IVertex, inputs::Vertex...) =
  spliceinput(v, group(inputs...))

# TODO: move away from this, it's unreliable
function graphinputs(v::IVertex)
  n = 0
  prewalk(v) do v
    isinput(v) && (n = max(n, value(v).n))
    v
  end
  return n
end

# Closures
# TODO: always close over a single tuple, remove need for arg count

import Base: ==

struct Lambda
  args::Int
  body::IVertex{Any}
end

a::Lambda == b::Lambda = a.args == b.args && a.body == b.body
Base.hash(a::Lambda, h::UInt) = hash(Lambda, hash(a.args, hash(a.body, h)))

function normclosures(ex)
  MacroTools.prewalk(shortdef(ex)) do ex
    @capture(ex, (args__,) -> body_) || return ex
    @assert all(arg -> isa(arg, Symbol), args)
    :($(Lambda(length(args), constant(nothing)))($body, $(args...)))
  end
end

function tovertex!(v, bs, f::Lambda, body, args...)
  closed = setdiff(collect(filter(x -> inexpr(body, x), keys(bs))), args)
  vars = [closed..., args...]
  v.value = Lambda(f.args, graphm(merge(bs, bindargs(vars)), body))
  thread!(v, graphm.(bs, closed)...)
end

function tocall(f::Lambda, closed...)
  ex = :(;)
  bind(x, s = gensym(:c)) = (push!(ex.args, :($s = $x)); s)
  closed = [x isa Expr ? bind(x) : x for x in closed]
  args = [gensym(:x) for _ in 1:f.args]
  vars = [closed..., args...]
  body = prewalk(f.body) do x
    isinput(x) ? constant(vars[value(x).n]) :
    x == constant(Input()) ? constant(:($(vars...),)) :
      x
  end
  push!(ex.args, Expr(:->, :($(args...),), unblock(syntax(body))))
  return unblock(ex)
end

# "Open" Closures

const uid = Ref(UInt64(0))

struct OLambda
  args::Int
  id::UInt64
end

OLambda(args) = OLambda(args, uid[] += 1)

struct LooseEnd
  id::UInt64
end

function λopen(l::Lambda, args...)
  l′ = OLambda(l.args)
  body = spliceinputs(l.body, args...,
                      [vertex(Split(i), constant(LooseEnd(l′.id))) for i = 1:l.args]...)
  vertex(l′, body)
end

λopen(v::IVertex) = λopen(value(v), inputs(v)...)

function λclose(l::OLambda, body)
  in = LooseEnd(l.id)
  vars = []
  body = prewalk(body) do v
    contains(v, in) && return v
    push!(vars, v)
    vertex(Split(l.args+length(vars)), constant(in))
  end
  body = map(x -> x == in ? Input() : x, body)
  # Swap arguments with variables
  body = spliceinputs(body,
                      [inputnode(i+length(vars)) for i = 1:l.args]...,
                      [inputnode(i) for i = 1:length(vars)]...) |> detuple
  vertex(Lambda(l.args, body), vars...)
end

λclose(v::IVertex) = λclose(value(v), inputs(v)...)
