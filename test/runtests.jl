using Test
using Earley
include("json.jl")

@testset "nullables()" begin
  g1 = CFG([
    :A => ['a'],
    :A => ['a', :A],
    :B => ['b'],
    :B => [:B, 'b']
  ])
  @test Earley.nullables(g1) == Set([])

  g2 = CFG([
    :A => [],
    :B => [:A, 'a'],
    :C => [:A, 'c'],
    :C => [:A, :A],
  ])
  @test Earley.nullables(g2) == Set([:A, :C])

  g3 = CFG([
    :A => [:D],
    :B => [:A],
    :C => [:B],
    :D => [:C],
    :D => []
  ])
  @test Earley.nullables(g3) == Set([:A, :B, :C, :D])

  g4 = CFG([
    :A => [:A]
  ])
  @test Earley.nullables(g4) == Set([])

  g5 = CFG([
    :A => [:D, :C, :B],
    :B => [:A, :A],
    :C => [:A, :B, :D],
    :D => [:D],
    :D => [:C, :C, :B],
    :A => []
  ])
  @test Earley.nullables(g5) == Set([:A, :B])

  g6 = CFG([
    :A => [],
    :A => [:A, 'a'],
    :B => [:A],
    :B => [:B, 'b'],
    :C => [:A, 'c', :B],
    :C => [:B, 'c', :A],
    :D => [:B],
    :D => [:C],
    :D => [:D, 'd']
  ])
  @test Earley.nullables(g6) == Set([:A, :B, :D])
end

@testset "Match" begin
  @testset "OneOf" begin
    @test matches(Match.OneOf("0123456789"), '0')
    @test matches(Match.OneOf("0123456789"), '3')
    @test matches(Match.OneOf("0123456789"), '8')
    @test !matches(Match.OneOf("0123456789"), 'x')
    @test !matches(Match.OneOf("0123456789"), "nine")

    @test matches(Match.OneOf(["if", "true", "false", "else"]), "if")
    @test matches(Match.OneOf(["if", "true", "false", "else"]), "true")
    @test !matches(Match.OneOf(["if", "true", "false", "else"]), "bool")
  end

  @testset "ASCII" begin
    @test matches(Match.ASCII(), 'a')
    @test matches(Match.ASCII(), 'X')
    @test matches(Match.ASCII(), '\r')
    @test matches(Match.ASCII(), ' ')
    @test matches(Match.ASCII(), '.')
    @test matches(Match.ASCII(), '0')
    @test matches(Match.ASCII(), '8')
    @test !matches(Match.ASCII(), 'α')
    @test !matches(Match.ASCII(), 'Σ')
    @test !matches(Match.ASCII(), 'す')
    @test !matches(Match.ASCII(), '🙈')
  end

  @testset "Space" begin
    @test !matches(Match.Space(), 'a')
    @test !matches(Match.Space(), 'X')
    @test matches(Match.Space(), '\r')
    @test matches(Match.Space(), ' ')
    @test !matches(Match.Space(), '.')
    @test !matches(Match.Space(), '0')
    @test !matches(Match.Space(), '8')
    @test !matches(Match.Space(), 'α')
    @test !matches(Match.Space(), 'Σ')
    @test !matches(Match.Space(), 'す')
    @test !matches(Match.Space(), '🙈')
  end

  @testset "Digit" begin
    @test !matches(Match.Digit(), 'a')
    @test !matches(Match.Digit(), 'X')
    @test !matches(Match.Digit(), '\r')
    @test !matches(Match.Digit(), ' ')
    @test !matches(Match.Digit(), '.')
    @test matches(Match.Digit(), '0')
    @test matches(Match.Digit(), '8')
    @test !matches(Match.Digit(), 'α')
    @test !matches(Match.Digit(), 'Σ')
    @test !matches(Match.Digit(), 'す')
    @test !matches(Match.Digit(), '🙈')
  end

  @testset "Letter" begin
    @test matches(Match.Letter(), 'a')
    @test matches(Match.Letter(), 'X')
    @test !matches(Match.Letter(), '\r')
    @test !matches(Match.Letter(), ' ')
    @test !matches(Match.Letter(), '.')
    @test !matches(Match.Letter(), '0')
    @test !matches(Match.Letter(), '8')
    @test matches(Match.Letter(), 'α')
    @test matches(Match.Letter(), 'Σ')
    @test matches(Match.Letter(), 'す')
    @test !matches(Match.Letter(), '🙈')
  end

  @testset "Lower" begin
    @test matches(Match.Lower(), 'a')
    @test !matches(Match.Lower(), 'X')
    @test !matches(Match.Lower(), '\r')
    @test !matches(Match.Lower(), ' ')
    @test !matches(Match.Lower(), '.')
    @test !matches(Match.Lower(), '0')
    @test !matches(Match.Lower(), '8')
    @test matches(Match.Lower(), 'α')
    @test !matches(Match.Lower(), 'Σ')
    @test !matches(Match.Lower(), 'す')
    @test !matches(Match.Lower(), '🙈')
  end

  @testset "Upper" begin
    @test !matches(Match.Upper(), 'a')
    @test matches(Match.Upper(), 'X')
    @test !matches(Match.Upper(), '\r')
    @test !matches(Match.Upper(), ' ')
    @test !matches(Match.Upper(), '.')
    @test !matches(Match.Upper(), '0')
    @test !matches(Match.Upper(), '8')
    @test !matches(Match.Upper(), 'α')
    @test matches(Match.Upper(), 'Σ')
    @test !matches(Match.Upper(), 'す')
    @test !matches(Match.Upper(), '🙈')
  end

  @testset "Print" begin
    @test matches(Match.Print(), 'a')
    @test matches(Match.Print(), 'X')
    @test !matches(Match.Print(), '\r')
    @test matches(Match.Print(), ' ')
    @test matches(Match.Print(), '.')
    @test matches(Match.Print(), '0')
    @test matches(Match.Print(), '8')
    @test matches(Match.Print(), 'α')
    @test matches(Match.Print(), 'Σ')
    @test matches(Match.Print(), 'す')
    @test matches(Match.Print(), '🙈')
  end

  @testset "HexDigit" begin
    @test matches(Match.HexDigit(), 'a')
    @test !matches(Match.HexDigit(), 'X')
    @test !matches(Match.HexDigit(), '\r')
    @test !matches(Match.HexDigit(), ' ')
    @test !matches(Match.HexDigit(), '.')
    @test matches(Match.HexDigit(), '0')
    @test matches(Match.HexDigit(), '8')
    @test !matches(Match.HexDigit(), 'α')
    @test !matches(Match.HexDigit(), 'Σ')
    @test !matches(Match.HexDigit(), 'す')
    @test !matches(Match.HexDigit(), '🙈')
  end

  @testset "AnyToken" begin
    @test matches(Match.AnyToken(), 'a')
    @test matches(Match.AnyToken(), 'X')
    @test matches(Match.AnyToken(), '\r')
    @test matches(Match.AnyToken(), ' ')
    @test matches(Match.AnyToken(), '.')
    @test matches(Match.AnyToken(), '0')
    @test matches(Match.AnyToken(), '8')
    @test matches(Match.AnyToken(), 'α')
    @test matches(Match.AnyToken(), 'Σ')
    @test matches(Match.AnyToken(), 'す')
    @test matches(Match.AnyToken(), '🙈')
    @test matches(Match.AnyToken(), "false")
    @test matches(Match.AnyToken(), 25)
  end

  @testset "Predicate" begin
    p(c) = isletter(c) || isdigit(c)
    M = Match.Predicate(p)
    @test matches(M, 'a')
    @test matches(M, 'X')
    @test !matches(M, '\r')
    @test !matches(M, ' ')
    @test !matches(M, '.')
    @test matches(M, '0')
    @test matches(M, '8')
    @test matches(M, 'α')
    @test matches(M, 'Σ')
    @test matches(M, 'す')
    @test !matches(M, '🙈')
  end

  @testset "Advanced OneOf" begin
    @test matches(Match.OneOf([Match.Lower(), Match.Digit()]), 'a')
    @test matches(Match.OneOf([Match.Lower(), Match.Digit()]), '0')
    @test matches(Match.OneOf([Match.Lower(), Match.Digit()]), '9')
    @test matches(Match.OneOf([Match.Lower(), Match.Digit()]), 'x')
    @test matches(Match.OneOf([Match.Lower(), Match.Digit()]), 'α')
    @test !matches(Match.OneOf([Match.Lower(), Match.Digit()]), 'A')
    @test !matches(Match.OneOf([Match.Lower(), Match.Digit()]), 'Z')
    @test !matches(Match.OneOf([Match.Lower(), Match.Digit()]), '!')

    @test matches(Match.OneOf([Match.OneOf(["true", "false"]), "bool"]), "true")
    @test matches(Match.OneOf([Match.OneOf(["true", "false"]), "bool"]), "bool")
    @test !matches(Match.OneOf([Match.OneOf(["true", "false"]), "bool"]), "int")
  end
end

@testset "recognize(::CFG)" begin
  grammar_par1 = CFG([
    :Par => [], # matches empty string
    :Par => ['(', :Par, ')'],
  ])
  @test recognize(grammar_par1, "")
  @test recognize(grammar_par1, "()")
  @test !recognize(grammar_par1, "(")
  @test !recognize(grammar_par1, ")")
  @test !recognize(grammar_par1, ")(")
  @test !recognize(grammar_par1, "(12)")
  @test recognize(grammar_par1, "((()))")
  @test !recognize(grammar_par1, "()()")
  @test recognize(grammar_par1, "(((((((((((((((((((((((((((((())))))))))))))))))))))))))))))")
  @test !recognize(grammar_par1, "((((((((((((((((((((((((((((())))))))))))))))))))))))))))))")
  @test !recognize(grammar_par1, "(((((((((((((((((((((((((((((()))))))))))))))))))))))))))))")

  grammar_par2 = CFG([
      :Par => [],
      :Par => ['(', :Par, ')'],
      :Par => ['[', :Par, ']'],
  ])
  @test recognize(grammar_par2, "")
  @test recognize(grammar_par2, "()")
  @test recognize(grammar_par2, "[]")
  @test !recognize(grammar_par2, "][")
  @test !recognize(grammar_par2, "12")
  @test recognize(grammar_par2, "(([()]))")
  @test recognize(grammar_par2, "([[([(())])]])")

  # left-recursive grammar matching an even number of 'a' characters
  grammar_a1 = CFG([
      :A => [],
      :A => [:A, 'a', 'a']
    ])
  @test recognize(grammar_a1, "")
  @test !recognize(grammar_a1, "a")
  @test recognize(grammar_a1, "aa")
  @test !recognize(grammar_a1, "aaa")
  @test recognize(grammar_a1, "aaaa")

  # right-recursive grammar matching an even number of 'a' characters
  grammar_a1 = CFG([
      :A => [],
      :A => ['a', 'a', :A]
    ])
  @test recognize(grammar_a1, "")
  @test !recognize(grammar_a1, "a")
  @test recognize(grammar_a1, "aa")
  @test !recognize(grammar_a1, "aaa")
  @test recognize(grammar_a1, "aaaa")

  # a simultaneously left-recursive, right-recursive, and ambiguous grammar
  grammar_a = CFG([
      :A => ['a'],
      :A => [:A, :A]
    ])
  @test !recognize(grammar_a, "")
  @test recognize(grammar_a, "a")
  @test !recognize(grammar_a, "ab")
  @test recognize(grammar_a, "aa")
  @test recognize(grammar_a, "aaa")
  @test recognize(grammar_a, "aaaa")
  @test recognize(grammar_a, "aaaaa")
  @test recognize(grammar_a, "aaaaaa")

  grammar_cyclic = CFG([
    :A => [:A]
  ])
  @test !recognize(grammar_cyclic, "")
  @test !recognize(grammar_cyclic, "a")
  @test !recognize(grammar_cyclic, "abc")
  @test !recognize(grammar_cyclic, "1234567890")

  grammar_nullable = CFG([
    :A => ['a'],
    :A => [:B, :A],
    :B => [],
    :B => [:A]
  ])
  @test recognize(grammar_nullable, "a")
  @test recognize(grammar_nullable, "aaa")

  grammar_ab = CFG([
    :AB => [Match.OneOf("ab")],
    :AB => [:AB, :AB]
  ])
  @test !recognize(grammar_ab, "")
  @test recognize(grammar_ab, "ab")
  @test recognize(grammar_ab, "ba")
  @test recognize(grammar_ab, "aa")
  @test recognize(grammar_ab, "bbbbbb")
  @test recognize(grammar_ab, "abababaabbba")
  @test recognize(grammar_ab, "abababaabbbaababbabababababababbababaaaaabbabbbbbb")
  @test !recognize(grammar_ab, "acb")

  grammar_decimal = CFG([
    :Decimal => [:Nonnegative],
    :Decimal => [Match.OneOf("+-"), :Nonnegative],
    :Nonnegative => [Match.Digit()],
    :Nonnegative => [Match.OneOf("123456789"), :Digits],
    :Digits => [],
    :Digits => [:Digits, Match.Digit()],
  ])
  @test !recognize(grammar_decimal, "")
  @test recognize(grammar_decimal, "0")
  @test recognize(grammar_decimal, "1")
  @test recognize(grammar_decimal, "2")
  @test recognize(grammar_decimal, "-0")
  @test recognize(grammar_decimal, "+5")
  @test recognize(grammar_decimal, "12389348279824792837492")
  @test recognize(grammar_decimal, "+12389348279824792837492")
  @test recognize(grammar_decimal, "-12389348279824792837492")
  @test !recognize(grammar_decimal, "09")
  @test !recognize(grammar_decimal, "023")
  @test !recognize(grammar_decimal, "0x42")
end

@testset "recognize(::CFG) large grammars" begin
  json = JSON.grammar.cfg

  @test Earley.nullables(json) == Set([:WS, :Members, :Values, Symbol("Optional Minus"), Symbol("Optional Fractional Part"), Symbol("Optional Exponent"), Symbol("Optional Sign"), :Chars])

  @test recognize(json, "{}")
  @test recognize(json, "[]")
  @test recognize(json, "[true]")
  @test recognize(json, """[""]""")
  @test recognize(json, """["green\\nしろ"]""")
  @test recognize(json, "[1]")
  @test recognize(json, "[-0]")
  @test recognize(json, "[123456789012345678901234567890]")
  @test recognize(json, "[2e6]")
  @test recognize(json, "[3.5]")
  @test recognize(json, "[-12.0]")
  @test recognize(json, "[true, null, false]")
  @test recognize(json, """{"twelve": null}""")
  @test recognize(json, """{ "α" :   7.3e-3\n,\n"R": 0.12820 }""")
  @test !recognize(json, "12")
  @test !recognize(json, "\"yellow\"")
  @test !recognize(json, "{true}")
  @test !recognize(json, "[FALSE]")
end

@testset "recognize(::Grammar)" begin
  grammar_par1 = Grammar([
    (:Par => [],               ()      -> error()),
    (:Par => [:Par, :Par],     (_,_)   -> error()),
    (:Par => ['(', :Par, ')'], (_,_,_) -> error()),
  ])
  @test recognize(grammar_par1, "")
  @test recognize(grammar_par1, "()")
  @test !recognize(grammar_par1, "(")
  @test !recognize(grammar_par1, ")")
  @test !recognize(grammar_par1, ")(")
  @test !recognize(grammar_par1, "(12)")
  @test recognize(grammar_par1, "((()))")
  @test recognize(grammar_par1, "()()")
  @test recognize(grammar_par1, "(((()()(()))))")
  @test !recognize(grammar_par1, "((((()(()))))")
  @test recognize(grammar_par1, "(((((((((((((((((((((((((((((())))))))))))))))))))))))))))))")
  @test !recognize(grammar_par1, "((((((((((((((((((((((((((((())))))))))))))))))))))))))))))")
  @test !recognize(grammar_par1, "(((((((((((((((((((((((((((((()))))))))))))))))))))))))))))")
end

@testset "checkgrammar()" begin
  g1 = CFG([
    :A => [:A],
    :A => []
  ])
  @test_throws ErrorException Earley.checkgrammar(g1)

  g2 = CFG([
    :A => [],
    :A => [:A]
  ])
  @test_throws ErrorException Earley.checkgrammar(g2)

  g3 = CFG([
    :A => [:B],
    :B => [:A],
    :A => ['a'],
    :B => ['b'],
  ])
  @test_throws ErrorException Earley.checkgrammar(g3)

  g4 = CFG([
    :A => [:A, 'a'],
    :A => ['a', :A],
    :A => [:A],
    :A => ['a']
  ])
  @test_throws ErrorException Earley.checkgrammar(g4)

  g5 = CFG([
    :A => [:B, :B],
    :B => ['a', 'b'],
    :B => [:A, :B],
    :A => [],
    :B => [:A, :A, :A],
  ])
  @test_throws ErrorException Earley.checkgrammar(g5)

  g6 = Grammar([
    (:A => [:A],  identity),
    (:A => ['a'], identity)
  ])
  @test_throws ErrorException Earley.checkgrammar(g6)

  g7 = Grammar([
    (:A => [:B],  identity),
    (:B => [:A],  identity),
    (:A => ['a'], identity),
    (:B => ['b'], identity)
  ])
  @test_throws ErrorException Earley.checkgrammar(g7)
end

@testset "parse(::CFG)" begin
  grammar_par = CFG([
      :Par => [],
      :Par => ['(', :Par, ')'],
      :Par => ['[', :Par, ']'],
  ])
  @testset "parens, \"\"" begin
    tree = parse(grammar_par, "")
    @test tree.rule == 1 && tree.start == 1 && tree.stop == 1 && isempty(tree.children)
  end
  @testset "parens, \"()\"" begin
    tree = parse(grammar_par, "()")
    @test tree.rule == 2 && tree.start == 1 && tree.stop == 3 && length(tree.children) == 3
    (child1, child2, child3) = tree.children
    @test child1.rule == 0 && child1.start == 1 && child1.stop == 2 && isempty(child1.children)
    @test child2.rule == 1 && child2.start == 2 && child2.stop == 2 && isempty(child2.children)
    @test child3.rule == 0 && child3.start == 2 && child3.stop == 3 && isempty(child3.children)
  end
  @testset "parens, \"([])\"" begin
    tree = parse(grammar_par, "([])")
    @test tree.rule == 2 && tree.start == 1 && tree.stop == 5 && length(tree.children) == 3
    (child1, child2, child3) = tree.children
    @test child1.rule == 0 && child1.start == 1 && child1.stop == 2 && isempty(child1.children)
    @test child2.rule == 3 && child2.start == 2 && child2.stop == 4 && length(child2.children) == 3
    @test child3.rule == 0 && child3.start == 4 && child3.stop == 5 && isempty(child3.children)
    (child21, child22, child23) = child2.children
    @test child21.rule == 0 && child21.start == 2 && child21.stop == 3 && isempty(child21.children)
    @test child22.rule == 1 && child22.start == 3 && child22.stop == 3 && isempty(child22.children)
    @test child23.rule == 0 && child23.start == 3 && child23.stop == 4 && isempty(child23.children)
  end
end

@testset "parse(::Grammar)" begin

  @testset "left/right recursive" begin
    gl = Grammar([
      (:A => [],        ()    -> []),
      (:A => [:A, 'a'], (e,a) -> [e, a])
    ])
    gr = Grammar([
      (:A => [],        ()    -> []),
      (:A => ['a', :A], (a,e) -> [a, e])
    ])
    glr = Grammar([
      (:A => [],            ()        -> []),
      (:A => [:A, 'a', :A], (e1,a,e2) -> [e1, a, e2])
    ])

    @test parse(gl,  "") == []
    @test parse(gr,  "") == []
    @test parse(glr, "") == []

    @test parse(gl,  "a") == [[], 'a']
    @test parse(gr,  "a") == ['a', []]
    @test parse(glr, "a") == [[], 'a', []]

    @test parse(gl,  "aa") == [[[], 'a'], 'a']
    @test parse(gr,  "aa") == ['a', ['a', []]]
    @test parse(glr, "aa") == [[], 'a', [[], 'a', []]]

    @test parse(gl,  "aaaaa") == [[[[[[], 'a'], 'a'], 'a'], 'a'], 'a']
    @test parse(gr,  "aaaaa") == ['a', ['a', ['a', ['a', ['a', []]]]]]
    #@test parse(glr, "aaaaa")
  end

  @testset "dangling else" begin
    # Two grammars for a trivial C-like syntax with dangling else ambiguity.
    # Depending on the order of the third and fourth rule, the ambiguity is resolved differently.
    ra = [
      (:Block => ["{}"],                           (_)       -> []),
      (:Block => [:If],                            e         -> e),
      (:If    => ["if()", :Block],                 (_,b)     -> ["if()", b]),
      (:If    => ["if()", :Block, "else", :Block], (_,c,_,a) -> ["if()", c, a])
    ]
    g_inner = Grammar{String}(ra)
    g_outer = Grammar{String}([ra[1], ra[2], ra[4], ra[3]])

    @test parse(g_inner, ["{}"]) == []
    @test parse(g_outer, ["{}"]) == []

    @test parse(g_inner, ["if()", "{}"]) == ["if()", []]
    @test parse(g_outer, ["if()", "{}"]) == ["if()", []]

    @test parse(g_inner, ["if()", "{}", "else", "{}"]) == ["if()", [], []]
    @test parse(g_outer, ["if()", "{}", "else", "{}"]) == ["if()", [], []]

    @test parse(g_inner, ["if()", "if()", "{}"]) == ["if()", ["if()", []]]
    @test parse(g_outer, ["if()", "if()", "{}"]) == ["if()", ["if()", []]]

    # This is where the ambiguity comes into play
    @test parse(g_inner, ["if()", "if()", "{}", "else", "{}"]) == ["if()", ["if()", [], []]]
    @test parse(g_outer, ["if()", "if()", "{}", "else", "{}"]) == ["if()", ["if()", []], []]
  end

  @testset "parse(::Grammar) large grammars" begin
    json = JSON.grammar
    @test parse(json, "{}") == Dict()
    @test parse(json, "[]") == []
    @test parse(json, "[123456789012345678901234567890]") == [123456789012345678901234567890]
    @test parse(json, "[-0]") == [0]
    @test parse(json, "[true, false, null]") == [true, false, nothing]
    @test parse(json, """{"twelve": null}""") == Dict("twelve" => nothing)
    @test parse(json, """{"\\r": [{}], "\\u03b1": "true"}""") == Dict("\r" => [Dict()], "α" => "true")
    @test isapprox(parse(json, "[3.14195e5, 13e-2]"), [314195, 0.13])
    @test parse(json, collect("""{ "α" :   "7.3e-3"\n,\n"R": "0.12820" }""")) == Dict("α" => "7.3e-3", "R" => "0.12820")
  end

  @testset "mixed associativity" begin
    g = Grammar([ # A simple arithmetic grammar with mixed associativity.
      (:expression => [:sum],      identity),
      (:expression => [:product],  identity),
      (:sum => [:sum, '+', :product], (e1,_,e2) -> Expr(:call, :+, e1, e2)),
      (:sum => [:sum, '-', :product], (e1,_,e2) -> Expr(:call, :-, e1, e2)),
      (:sum => [:product],                   identity),
      (:product => [:factor],                identity),
      (:product => [:product, '*', :factor], (e1,_,e2) -> Expr(:call, :*, e1, e2)),
      (:factor => [:number], identity),
      (:factor => [:power],  identity),
      (:factor => ['(', :expression, ')'], (_,e,_) -> e),
      (:number => [Match.Digit()], c -> c-'0'),
      (:power => [:factor, '^', :factor], (e1,_,e2) -> Expr(:call, :^, e1, e2)),
    ]);

    @test parse(g, "1-2-3") == :((1-2)-3)
    @test parse(g, "2*3*4") == :((2*3)*4)
    @test parse(g, "2^3^4") == :(2^(3^4))
    @test parse(g, "1+2-3+4") == :(((1+2)-3)+4)
    @test parse(g, "2*3^4^(5+6)*7") == :((2*3^(4^(5+6)))*7)
    @test parse(g, "1-2*3^4+5") == :((1-2*3^4)+5)
  end
end
