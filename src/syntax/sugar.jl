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

splitnode(v, n) = vertex(Split(n), v)

inputnode(n) = splitnode(constant(Input()), n)

isinput(v::IVertex) = isa(value(v), Split) && isconstant(v[1]) && value(v[1][1]) == Input()

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

function graphinputs(v::IVertex)
  n = 0
  prewalk(v) do v
    isinput(v) && (n = max(n, value(v).n))
    v
  end
  return n
end

# Closures

struct Flosure end
struct LooseEnd end

# TODO: scope
function normclosures(ex)
  bs = bindings(ex)
  MacroTools.prewalk(shortdef(ex)) do ex
    @capture(ex, (args__,) -> body_) || return ex
    @assert all(arg -> isa(arg, Symbol), args)
    closed = filter(x -> inexpr(body, x), bs)
    vars = vcat(closed, args)
    body = MacroTools.prewalk(body) do ex
      ex in vars ?
        Expr(:call, Split(findfirst(x->x==ex, vars)), LooseEnd()) :
        ex
    end
    :($(Flosure())($body, $(closed...)))
  end |> MacroTools.flatten |> block
end

# TODO: nested closures
flopen(v::IVertex) = map(x->x==LooseEnd()?Input():x,v)
