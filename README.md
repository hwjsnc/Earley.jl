Earley.jl
=========

Parse context-free languages with Earley's algorithm.

Examples
--------

```julia
julia> grammar = Grammar([ # Decimal numbers with an optional sign
           (:Number   => [:Unsigned],                     identity),
           (:Number   => [Match.OneOf("+-"), :Unsigned],  (c, n) -> (c == '+') ? n : -n),
           (:Unsigned => [Match.Digit()],                 d      -> d - '0'),
           (:Unsigned => [:Unsigned, Match.Digit()],      (n, d) -> 10n + (d-'0')),
       ]);

julia> parse(grammar, "-12")
-12
```

```julia
julia> grammar = Grammar([ # s-expressions
           (:sexpr  => [:par_open, :values, :par_close],  (_, values, _)   -> tuple(values...)),
           (:value  => [:identifier],                     identity),
           (:value =>  [:sexpr],                          identity),
           (:values => [],                                ()               -> []),
           (:values => [:ws, :values, :ws, :value, :ws],  (_, vs, _, v, _) -> push!(vs, v)),
           (:identifier => [Match.Letter()],              c                -> string(c)),
           (:identifier => [:identifier, Match.Letter()], (i, c)           -> i * c),
           (:par_open => [:ws, '(', :ws],                 (_, _, _)        -> nothing),
           (:par_close => [:ws, ')', :ws],                (_, _, _)        -> nothing),
           (:ws => [],                                    ()               -> nothing),
           (:ws => [Match.Space(), :ws],                  (_, _)           -> nothing),
       ]);

julia> parse(grammar, "(abc (def ghi) (j))")
("abc", ("def", "ghi"), ("j",))
```

```julia
julia> g = Grammar([ # A simple arithmetic grammar with mixed associativity.
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

julia> parse(g, "1+2-3+4")
:(((1 + 2) - 3) + 4)

julia> parse(g, "2*3^4^(5+6)*7")
:((2 * 3 ^ (4 ^ (5 + 6))) * 7)

julia> parse(g, "1-2*3^4+5")
:((1 - 2 * 3 ^ 4) + 5)
```

```julia
julia> grammar = CFG([ # An even number of 'a' characters
           :A => [:A, :A],
           :A => ['a', 'a']
           :A => [],
       ]);

julia> recognize(grammar, "aaa")
false

julia> recognize(grammar, "aaaa")
true
```


Overview
--------

This package provides the following:

* `CFG`, a datatype for modeling context-free grammars.

* `Grammar`, a datatype for modeling context-free grammars and semantic actions associated with each production rule; i.e. a grammar with synthesized attributes.

* `recognize(grammar, input)`, a function that can tell for any grammar and any input, whether the input belongs to the language defined by the grammar.

* `parse(grammar, input)`, a function that can parse a given input and return either a parse tree, or a value computed through semantic actions.

* `matches`, a function that matches input tokens against terminals listed in the production rules.

* `Matches`, various predefined token classes.

For detailed information, see the respective Julia docstrings.


Compatibility
-------------

`Earley.jl` follows [semanting versioning v2.0.0](https://semver.org/).
The current version is 1.0.0.

This package works with Julia version 1.6.7 (the current LTS) and above.
It should also work for Julia version 1.0.

It depends on the [DataStructures](https://github.com/JuliaCollections/DataStructures.jl) package.


Releases
--------

### Version 1.0.0

Initial public version


Bugs, Caveats, TODO
-------------------

- Performance has only been a minor consideration during the development of this package.
  Some of the included algorithms have asymptotically faster alternatives which are not implemented here.

- There is no support for repeated or optional terms, such as `A ::= 'a' *` from EBNF.
  It's up to the user to translate constructs such as this into the form required for recognition/parsing.

- The parser does not support cyclic grammars.
  (The recognizer does.)
  It seems feasible to add support for cyclic grammars in principle, but it would require a lot of effort and the payoff would be questionable.

- In the case of ambiguous languages, the parser can only return one parse tree, not the whole parse forest.

- There is no support for reporting partial parses or likely fixes in the case of minor syntax errors.

- Error messages for incorrect grammars may be hard to decipher.


See also
--------

A [tutorial by Loup Vaillant](https://loup-vaillant.fr/tutorials/earley-parsing/) has been helpful to the author in understanding the principles of Earley parsing.


Copyright
---------

Ⓒ Lukas Himbert 2022

Licensed under the [EUPL-1.2-or-later](https://joinup.ec.europa.eu/collection/eupl/eupl-text-eupl-12).
