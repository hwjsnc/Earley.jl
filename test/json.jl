module JSON

using DataStructures
using Earley

# This is a JSON grammar translated from augmented BNF in RFC 4627.
# It should not be assumed to be correct and is only used to test the Earley parser.
grammar = Grammar([
  # JSON text
  (:JSON => [:Object], identity),
  (:JSON => [:Array],  identity),

  # Structural characters
  (Symbol("Begin Array")     => [:WS, '[', :WS], (_,_,_) -> nothing),
  (Symbol("Begin Object")    => [:WS, '{', :WS], (_,_,_) -> nothing),
  (Symbol("End Array")       => [:WS, ']', :WS], (_,_,_) -> nothing),
  (Symbol("End Object")      => [:WS, '}', :WS], (_,_,_) -> nothing),
  (Symbol("Name Separator")  => [:WS, ':', :WS], (_,_,_) -> nothing),
  (Symbol("Value Separator") => [:WS, ',', :WS], (_,_,_) -> nothing),
  (:WS => [],                                    ()      -> nothing),
  (:WS => [:WS, Match.Space()],                  (_,_)   -> nothing),

  # Values
  (:Value => [:Object],        identity),
  (:Value => [:Array],         identity),
  (:Value => [:Number],        identity),
  (:Value => [:String],        identity),
  (:Value => collect("false"), (_...) -> false),
  (:Value => collect("null"),  (_...) -> nothing),
  (:Value => collect("true"),  (_...) -> true),

  # Objects
  (:Object  => [Symbol("Begin Object"), :Members, Symbol("End Object")], (_, members, _) -> OrderedDict(members)),
  (:Members => [],                                             ()       -> Pair{Any,Any}[]),
  (:Members => [:Member],                                      m        -> Pair{Any,Any}[m]),
  (:Members => [:Members, Symbol("Value Separator"), :Member], (ms,_,m) -> vcat(ms, [m])),
  (:Member  => [:String, Symbol("Name Separator"), :Value],    (s,_,v) -> (s=>v)),

  # Arrays
  (:Array  => [Symbol("Begin Array"), :Values, Symbol("End Array")], (_,vs,_) -> vs),

  (:Values => [],                                           ()       -> Any[]),
  (:Values => [:Value],                                     (v)      -> Any[v]),
  (:Values => [:Values, Symbol("Value Separator"), :Value], (vs,_,v) -> vcat(vs, [v])),

  # Numbers
  (:Number => [Symbol("Optional Minus"), :Int, Symbol("Optional Fractional Part"), Symbol("Optional Exponent")], (s,x,f,e) -> s * parse(BigFloat, "$x.$(f)") * 10^e),
  (Symbol("Optional Minus") => [],    ()  -> 1),
  (Symbol("Optional Minus") => ['-'], (_) -> -1),
  (:Int => [Match.Digit()],                     (c)     -> string(c)),
  (:Int => [Match.OneOf("123456789"), :Digits], (c, ds) -> c * ds),
  (Symbol("Optional Fractional Part") => [],             ()     -> "0"),
  (Symbol("Optional Fractional Part") => ['.', :Digits], (_,ds) -> ds),
  (:Digits => [Match.Digit()],          (c)    -> string(c)),
  (:Digits => [Match.Digit(), :Digits], (c,ds) -> c * ds),
  (Symbol("Optional Exponent") => [],                                                    () -> 0),
  (Symbol("Optional Exponent") => [Match.OneOf("eE"), Symbol("Optional Sign"), :Digits], (_,s,ds) -> s * parse(BigFloat, ds)),
  (Symbol("Optional Sign") => [],    ()  -> 1),
  (Symbol("Optional Sign") => ['+'], (_) -> 1),
  (Symbol("Optional Sign") => ['-'], (_) -> -1),

  # Strings
  (:String  => ['"', :Chars, '"'], (_, s, _) -> s),
  (:Chars   => [],                 ()        -> ""),
  (:Chars   => [:Chars, :Char],    (cs,c)    -> cs * c),
  (:Char    => [Match.Predicate(c -> (0x20 ≤ Int(c) ≤ 0x21) || (0x23 ≤ Int(c) ≤ 0x5b) || (0x5d ≤ Int(c) ≤ 0x10ffff))], identity),
  (:Char    => [:Escaped], c -> string(c)),
  (:Escaped => ['\\', Match.OneOf("\"\\/bfnrt")], (_,c) -> unescape_string("\\$c")),
  (:Escaped => ['\\', 'u', Match.HexDigit(), Match.HexDigit(), Match.HexDigit(), Match.HexDigit()], (_,_,cs...) -> unescape_string("\\u" * String(collect(cs)))),
])

end
