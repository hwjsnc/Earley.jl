"""`Earley`

`Earley` contains a recognizer and parser for context-free grammars.

Context-free grammars are modeled using the `CFG` datatype (preferred for
the recognizer) or the `Grammar` datatype (preferred for the parser). The
`Grammar` type includes a semantic action for each production rule of the
grammar.

The module provides the following functionality:

* `recognize(grammar, input)` checks if the `input` matches the language
  described by the `grammar`.

* `parse(grammar :: Grammar, input)` parses the `input` and computes the
  semantic actions on the parse tree.

* `parse(grammar :: CFG, input)` parses the `input` and returns a `ParseTree`.

* `matches(class, token)` is used by the algorithm to match a token (in the
  input) against a terminal/token class (in the right-hand side of a
  production rule). Some terminals are predefined in the `Match` submodule.

`recognize` supports all context-free grammars.

`parse` supports most practical grammars, including those with left-recursion,
right-recursion, mixed recursion, and ambiguity. However, cyclic grammars are
not supported as these may generate an infinite parse tree for a finite input.
"""
module Earley

using DataStructures: Stack
using DataStructures: Queue, enqueue!, dequeue!
using DataStructures: OrderedSet

include("Match.jl")
using .Match

import Base.parse

export CFG
export Grammar
export matches
export Match
export recognize



### CFG datatype

"""`CFG{T}(rules[, start_symbol])`

A context-free grammar with terminals of type `T` (usually `Any`). If no
`start_symbol` is given, the lhs of the first rule in `rules` is assumed.

`rules` is an array of production rules in the form of tuples `(A => rhs)`,
where `A` is a nonterminal (a `Symbol`) and `rhs` is an array of terminals (of
any type) and nonterminals.

Examples
========

```
CFG{Char}([
  :A => ['a'],
  :A => [:A, :A]
]);
```
is an ambiguous grammar that matches any (nonzero) number of 'a' characters.

```
CFG{String}([
  :Block => ["{}"],
  :Block => ["if()", :Block],
  :Block => ["if()", :Block, "else", :Block],
]);
```
is a grammar that matches a trivial C-like language with "dangling else"
ambiguity. Unlike the previous example, input tokens are strings rather than
Chars.

```
CFG([
  :Number => [Match.Digit()],
  :Number => [Match.Digit(), :Number]
]);
```
matches an unsigned decimal number. The paramater `T` is assumed to be
`Any`.
"""
struct CFG{T}
  rules :: Vector{Pair{Symbol,Vector{Union{Symbol,T}}}}
  start_symbol :: Symbol
  function CFG{T}(rules, start_symbol) where {T}
    return new{T}([lhs => collect(Union{Symbol,T}, rhs) for (lhs, rhs) in rules], start_symbol)
  end
end

CFG{T}(rules) where {T} = CFG{T}(rules, first(rules)[1])

# Assume tokens to be of type Any unless requested otherwise.
CFG(rules) = CFG{Any}(rules, first(rules)[1])
CFG(rules, start_symbol) = CFG{Any}(rules, start_symbol)



### Grammar datatype

"""`Grammar{T}(rules_and_actions[; start_symbol])`

A context-free grammar with terminals of type `T` (usually `Any`), as well as
a list of semantic actions (i.e. functions). `start_symbol` is an optional
argument specifying the start symbol (that needs to match the whole input). If
no value is supplied, the left-hand side of the first production rule is
assumed.

The list of rules and actions should be an iterable of tuples
`(lhs => rhs, action)`, where `lhs => rhs` is a production rule of a context
free grammar as described in the documentation for `CFG`. In short, `lhs`
should be a `Symbol` (nonterminal) and `rhs` should be an array of `Symbol`s
and terminals (which may be compared to the input using `matches`). The
`action` should be a function taking one argument for each terms on the
`rhs` of the rule and returning a single value.

In formal terms, `Grammar` describes an attribute grammar with synthesized
attributes, and the semantic actions are closures which define the attributes.

Example
=======

```
julia> g_num = Grammar([
  (:Number   => [:Unsigned],                 n      -> n),
  (:Number   => ['+', :Unsigned],            (_, n) -> n),
  (:Number   => ['-', :Unsigned],            (_, n) -> -n),
  (:Unsigned => [Match.Digit()],             d      -> (d - '0')),
  (:Unsigned => [:Unsigned, Match.Digit()],  (n, d) -> 10n + (d - '0'))
]);
```
matches a decimal integer (with optional sign) and computes its value.
"""
struct Grammar{T}
  cfg :: CFG{T}
  actions :: Vector{Function}

  function Grammar{T}(g, start_symbol::Symbol) where {T}
    new{T}(CFG{T}((rule for (rule, _) in g), start_symbol), Function[action for (_, action) in g])
  end
end

function Grammar{T}(g) where {T}
  ((start_symbol, _), _) = first(g)
  return Grammar{T}(g, start_symbol)
end

Grammar(g) = Grammar{Any}(g)
Grammar(g, s::Symbol) = Grammar{Any}(g, s)



### Earley Item datatype

"""`Item(start, rule, dot)`

Earley parser item, i.e. a compact representation of a partial parse.

* `start` is the position in the token stream where the partial parse begins,
  i.e. `start` is one if the parse starts at the first input token, two if it
  starts at the second input token, etc.
* `rule` is the index of the rule being parsed in the list of rules, i.e. one
  for the first rule, two for the second rule, etc.
* `dot` is the position of the 'dot' (in the common abstract notation of the
  algorithm), i.e. which sub-parse we're expecting next. The value is one if
  we need to try the first sub-parse, two if we need to try the second
  sub-parse, and equal to one plus the number of terms on the right-hand side
  if the sub-parse has been completed successfully.
"""
struct Item
  start :: Int
  rule :: Int
  dot :: Int
end


### recognizer

"""`recognize(grammar::CFG, input)`

Returns true if the input matches the given `grammar`, false otherwise. The
`input` shall be an array of tokens (e.g. Char, UInt8, String, …).

Terminal input tokens are matched against token classes using `match`. The
default implemantation compares equality (i.e. if a token is present in the
right hand side of a production rule, that token must be matched in the input
for the rule to match), but `match` can be overloaded to create custom token
classes for convenience. For predefined classes, see `Earley.Match`.

There is no restriction on the `grammar`, except that it must be context-free.

Examples
--------

```
julia> recognize(
  CFG([
    :Par => ['(', :Par, ')'],
    :Par => []
    ]),
  "(()))"
  )
false
```

```
julia> recognize(
  CFG([
    :Num => ['0', 'x', :Digits],
    :Digits => [Match.HexDigit()],
    :Digits => [Match.HexDigit(), :Digits],
    ]),
  "0xc0ffee"
  )
true
```
"""
function recognize(grammar :: CFG, input) :: Bool
  successful(item) = let
    (lhs, rhs) = grammar.rules[item.rule]
    return item.start == 1 && lhs == grammar.start_symbol && item.dot > length(rhs)
    end
  return any(successful, last(chart(grammar :: CFG, input)))
end


"""`recognize(grammar :: Grammar, input)`

Returns true if the input matches the given grammar, false otherwise. Semantic
actions associated with the production rules are ignored.
"""
function recognize(grammar :: Grammar, input) :: Bool
  recognize(grammar.cfg, input)
end


"""`chart(grammar :: CFG, input)`

Core implementation of the Earley algorithm.

Computes an Earley chart (list of attempted partial parses). This works for
any context-free `grammar` (as described in `CFG`) and `input`. `input` may be
an arbitrary iterator.
"""
function chart(grammar :: CFG, input)
  # The array `items` holds the partial parses in form of Earley items (struct `Item`).
  # The first entry is an array with all (attempted) complete parses,
  # the second entry is an array with all sub-parses after the first token has been consumed,
  # the third entry is an array with all sub-parses after the second token has been consumed,
  # and so on.
  items = [OrderedSet{Item}() for _ in 1:length(input)+1]

  null = nullables(grammar)

  # We start parsing from the start symbol
  for (i, (lhs, _)) in enumerate(grammar.rules)
    if lhs == grammar.start_symbol
      push!(items[1], Item(1, i, 1))
    end
  end

  # Continue all possible partial parses, one token at a time
  for (i, token) in enumerate(input)
    for item in items[i]
      (lhs, rhs) = grammar.rules[item.rule]
      if item.dot > length(rhs)
        complete!(items, i, grammar, item)
      else
        if rhs[item.dot] isa Symbol
          predict!(items, i, grammar, item, null)
        elseif matches(rhs[item.dot], token)
          scan!(items, i, grammar, item)
        else
          # partial parse failed, can't continue
        end
      end
    end
  end

  # final predict/complete after input has been consumed
  for item in last(items)
    (lhs, rhs) = grammar.rules[item.rule]
    if item.dot > length(rhs)
      complete!(items, length(items), grammar, item)
    elseif rhs[item.dot] isa Symbol
      predict!(items, length(items), grammar, item, null)
    else
      # we're stuck
    end
  end

  return items
end

function complete!(items, current, grammar, item)
  (completed_term, completed_term_rhs) = grammar.rules[item.rule]
  @assert item.dot > length(completed_term_rhs)

  for it in items[item.start]
    (lhs, rhs) = grammar.rules[it.rule]
    if it.dot <= length(rhs) && rhs[it.dot] == completed_term
      push!(items[current], Item(it.start, it.rule, it.dot+1))
    end
  end
end

function predict!(items, current, grammar, item, nullableset)
  (lhs, rhs) = grammar.rules[item.rule]
  @assert rhs[item.dot] isa Symbol

  if rhs[item.dot] in nullableset
    # we know that the current nonterminal can produce the empty string, so we can already advance the 'dot' over it.
    push!(items[current], Item(item.start, item.rule, item.dot+1))
  end

  for (i, (term, _)) in enumerate(grammar.rules)
    if term == rhs[item.dot]
      push!(items[current], Item(current, i, 1))
    end
  end
end

function scan!(items, current, grammar, item)
  push!(items[current+1], Item(item.start, item.rule, item.dot+1))
end


"""`nullables(grammar)`

Given a `grammar` (as described in `recognize`), return an array of nullable
nonterminals, i.e. nonterminals that can produce the empty string.
"""
function nullables(grammar :: CFG{T}) where {T}
  # TODO: currently this function has worst case time complexity O(length(grammar.rules)^3). A better technique is described in https://github.com/jeffreykegler/kollos/blob/master/notes/misc/loup2.md
  null = Set{Symbol}()
  # keep adding nullables until no further ones are found
  while true
    got_one = false
    for (lhs, rhs) in grammar.rules
      if (!(lhs in null)) && all(term -> term in null, rhs)
        push!(null, lhs)
        got_one = true
      end
    end
    if !got_one
      break
    end
  end
  return null
end

nullables(grammar :: Grammar) = nullables(grammar.cfg)



### Parser datatypes

"""`CompletedItem(start, stop, rule)`

Compact representation of a completed partial parse.

* `start` is the position in the token stream where the partial parse begins,
  i.e. `start` is one if the parse starts at the first token, etc.
* `stop` is the position in the token stream where the partial parse ends,
  i.e. `stop` is one if the parse stops before the first token, two if it
  stops after the first token, three if it stops after the second token, etc.
* `rule` is the index of the rule being parsed in the list of rules, i.e. one
  for the first rule, two for the second rule, etc.
  The value `0` may be used as a sentinel to mark a nonterminal where
  appropriate.
"""
struct CompletedItem
  start :: Int
  stop :: Int
  rule :: Int # May be `0` iff it corresponds to a terminal on the RHS of a production rule.
end


"""`ParseTree`

Data structure representing a parse tree, or a node therein. The following
members may be accessed:

- `rule`: Index of the rule corresponding to this node in the tree. Values 1
  through `length(rules)` are used for actual rules, `0` is used for
  matched terminals.
- `start`: Start index of the subset of the input represented by this node.
- `stop`: One plus the last index of the subset of the input represented by
  this node. If `stop` == `start`, the node matches an empty subset. If
  `rule == 0` (i.e. the node corresponds to a terminal), `stop = start+1`,
  and `start` is the index of the terminal in the input.
- `children :: Vector{ParseTree}`: A ParseTree (node) for each term on the
  right-hand side of the production `rule`, in order. For terminals, this
  will be empty.
"""
struct ParseTree
  rule :: Int # May be `0` iff it corresponds to a terminal on the RHS of a production rule.
  start :: Int
  stop :: Int
  children :: Vector{ParseTree}
end



### Parser

"""`process_chart_for_parser(grammar::CFG, chart)`

Processes the chart (list of partial parses) for later use by the parser. The
core Earley algorithm returns a list of partial parses, some of which are
complete, and some of which are not. The parser only needs completed partial
parses and also needs (or at least prefers) them indexed differently.

This function takes a list of lists of Earley items where the outer list
implicitely stores the _last_ token consumed and returns a list of lists of
Earley items where every item corresponds to a _completed_ partial parse and
the outer list implicitely stores the _first_ token consumed. Moreover, the
inner lists are sorted by rule, from smallest rule index to largest.
"""
function process_chart_for_parser(grammar :: CFG, chart)
  completed = [Vector{CompletedItem}() for _ in 1:length(chart)]
  for (stop, items) in enumerate(chart)
    for item in items
      (lhs, rhs) = grammar.rules[item.rule]
      if item.dot > length(rhs)
        push!(completed[item.start], CompletedItem(item.start, stop, item.rule))
      end
    end
  end
  for items in completed
    sort!(items; by=item->item.rule)
  end
  return completed
end

"""`parse(grammar::Grammar, input)`

Parse the given `input` according to the production rules and semantic actions
in `Grammar`, returning the result of the semantic action corresponding to the
rule that matches the whole input.

If the `grammar` is ambiguous, the parser will always use the first matching
rule to resolve the ambiguity.

Cyclic grammars are not supported as these can produce an infinite parse tree
for a finite input. Ambiguity, left-recursion and/or right-recursion do not
generally problem for the parser. All unambiguous context-free grammars are
supported.

Examples
========

```
julia> g_num = Grammar([
  (:Number   => [:Unsigned],                 n      -> n),
  (:Number   => ['+', :Unsigned],            (_, n) -> n),
  (:Number   => ['-', :Unsigned],            (_, n) -> -n),
  (:Unsigned => [Match.Digit()],             d      -> (d - '0')),
  (:Unsigned => [:Unsigned, Match.Digit()],  (n, d) -> 10n + (d - '0'))
]);
```
matches a decimal integer (with optional sign) and computes its value:
```
julia> parse(g_num, "42")
42

julia> parse(g_num, "-3141")
-3141
```

```
julia> g_num = Grammar{String}([
  (:Block => ["{}"],                           _         -> ()),
  (:Block => ["if()", :Block],                 (args...) -> args),
  (:Block => ["if()", :Block, "else", :Block], (args...) -> args),
]);
```
is a trivial C-like grammar with "dangling else" ambiguity. The input is
a list of `String`s rather than a string (of `Char`s):
```
julia> parse(g_num, ["if()", "if()", "{}", "else", "{}"])
("if()", ("if()", (), "else", ()))
```

```
julia> g = Grammar([
  (:A => [:A],  identity),
  (:A => ['a'], identity),
  ]);
```
is a cyclic grammar and is unsupported.
"""
function Base.parse(grammar :: Grammar, input)
  checkgrammar(grammar)
  completed_chart = process_chart_for_parser(grammar.cfg, chart(grammar.cfg, input))
  for item in first(completed_chart)
    if item.stop > length(input) && grammar.cfg.rules[item.rule][1] == grammar.cfg.start_symbol
      return do_parse(grammar, input, completed_chart, item)
    end
  end
  error("no parse")
end


"""`parse(grammar :: CFG, input)`

Parse a given `input`, returning a `ParseTree`.

The method `parse(::Grammar, input)` should be preferred to this one in most
cases. The same restrictions on the `grammar` apply to both methods.
"""
function Base.parse(grammar :: CFG, input)
  checkgrammar(grammar)
  completed_chart = process_chart_for_parser(grammar, chart(grammar, input))
  for item in first(completed_chart)
    if item.stop > length(input) && grammar.rules[item.rule][1] == grammar.start_symbol
      return do_parse(grammar, input, completed_chart, item)
    end
  end
  error("no parse")
end


function do_parse(grammar :: CFG, input, chart, item)
  if item.rule == 0
    return ParseTree(item.rule, item.start, item.stop, ParseTree[])
  else
    return ParseTree(item.rule, item.start, item.stop, [do_parse(grammar, input, chart, it) for it in decompose(grammar, input, chart, item)])
  end
end

function do_parse(grammar :: Grammar, input, chart, item)
  if item.rule == 0
    return input[item.start]
  else
    return grammar.actions[item.rule]((do_parse(grammar, input, chart, it) for it in decompose(grammar.cfg, input, chart, item))...)
  end
end


"""`finditems(grammar, chart, term, start, stop)`

Return an iterable of all valid parses of the nonterminal `term` starting at
`start` and ending before `stop`. `chart` must be a processed set of completed
earley items as returned by `process_chart_for_parser()`.

The items are sorted by rule index, then by length.
"""
function finditems(grammar, chart, term, start, stop)
  result = CompletedItem[]
  if start > stop
    return result
  end
  for item in chart[start]
    (lhs, _) = grammar.rules[item.rule]
    if item.stop ≤ stop && lhs == term
      push!(result, item)
    end
  end
  sort!(result, lt=(it1, it2)->it1.rule < it2.rule || it1.stop < it2.stop, alg=Base.Sort.DEFAULT_STABLE)
  return result
end


"""`decompose(grammar::CFG, input, chart, item)`

Given a completed Earley `item`, return a list of completed items, with each
element corresponding to the right-hand side of the `item.rule` in the
`grammar`.
"""
function decompose(grammar :: CFG, input, chart, item) :: Vector{CompletedItem}
  (lhs, rhs) = grammar.rules[item.rule]

  if isempty(rhs)
    return CompletedItem[]
  end

  # The workstack is a list of items to be considered for every term on the right-hand side of the production rule.
  # The bottom-most element is a list of possible items for the first rule on the rhs, the one above it is a list of possible items for the second rule on the rhs, etc.
  workstack = Stack{Queue{CompletedItem}}()

  # `items` is a list of possible completed items for every term on the rhs so far. Parses are matched greedily, one term at a time, until a match is definitely known to fail.
  # In that case, we back up one term and try the next candidates.
  items = Stack{CompletedItem}()

  # Populate the initial workstack
  if first(rhs) isa Symbol
    push!(workstack, Queue{CompletedItem}())
    for item in finditems(grammar, chart, first(rhs), item.start, item.stop)
      enqueue!(first(workstack), item)
    end
  elseif matches(first(rhs), input[item.start])
    push!(workstack, Queue{CompletedItem}())
    enqueue!(first(workstack), CompletedItem(item.start, item.start+1, 0))
  else
    error("This should never happen")
  end

  # Find appropriate items, one at a time.
  while !isempty(workstack)
    @assert length(workstack) == length(items) + 1
    if length(items) == length(rhs) && first(items).stop == item.stop
      return collect(Iterators.reverse(items))
    end
    if !isempty(first(workstack)) && length(items) < length(rhs)
      # try to match the next item
      it = dequeue!(first(workstack))
      if it.stop ≤ item.stop
        push!(items, it)
        next_candidates = Queue{CompletedItem}()
        push!(workstack, next_candidates)
        if length(items) < length(rhs)
          next_term = rhs[length(items)+1]
          if next_term isa Symbol
            # Matching nonterminal rules
            for i in finditems(grammar, chart, next_term, it.stop, item.stop)
              enqueue!(next_candidates, i)
            end
          elseif it.stop ≤ length(input) && matches(next_term, input[it.stop])
            # Matching  terminal
            enqueue!(next_candidates, CompletedItem(it.stop, it.stop+1, 0))
          end
        end
      end
    else
      # backtrack
      pop!(workstack)
      pop!(items)
    end
  end
  error("No solution - this should never happen")
end


### check grammar
"""`checkgrammar(grammar)`

Check if a given grammar can be parsed meaningfully. If the grammar is ok,
nothing will be returned and no action will be performed.

If any term appearing on the right-hand side of a production has no rule with
that term appearing on the left-hand side of a production, a warning will be
emitted.

If the grammar is cyclic (allows for a derivation A => A for any nonterminal
A, transitively), an `ErrorException` will be raised.
"""
function checkgrammar(grammar :: CFG)
  # TODO: check for symbols on the lhs that cannot be reached from the start symbol

  # Check for "undefined" nonterminals
  lhss = Set(lhs for (lhs, rhs) in grammar.rules)
  rhss = Set(term for (lhs, rhs) in grammar.rules for term in rhs if term isa Symbol)
  if !issubset(rhss, lhss)
    @warn "Symbol does not appear on the left-hand side of any production: $(first(setdiff(rhss, lhss)))"
  end

  if iscyclic(grammar)
    error("grammar is cyclic") # TODO: include the actual cycle in the error message
  end
end

checkgrammar(grammar :: Grammar) = checkgrammar(grammar.cfg)


"""`iscyclic(grammar)`

Returns true iff the grammar is cyclic, i.e. allows for derivation of A ⇒* A,
where A is a nonterminal and ⇒* means performing an arbitrary number of
replacements according to the production rules.
"""
function iscyclic(grammar :: CFG)
  ns = nullables(grammar) # TODO: avoid computing this twice
  isnullable(term) = term in ns
  # generate a list of replacement rules
  replacement_rules = Dict{Symbol,Set{Symbol}}()
  for (term1, rhs) in grammar.rules
    replacement_rules[term1] = get(replacement_rules, term1, Set{Symbol}())
    for (i, term2) in enumerate(rhs)
      if term2 isa Symbol && all(isnullable, rhs[1:i-1]) && all(isnullable, rhs[i+1:end])
        push!(replacement_rules[term1], term2)
      end
    end
  end
  # find cycles
  for term in keys(replacement_rules)
    visited = Set{Symbol}()
    next = replacement_rules[term]
    while !isempty(next)
      if term in next
        return true
      end
      union!(visited, next)
      next = setdiff(union((get(replacement_rules, t, Set{Symbol}()) for t in visited)...), visited)
    end
  end
  return false
end

iscyclic(grammar :: Grammar) = iscyclic(grammar.cfg)


### Debugging helper functions

"""`printchart(grammar, chart)`

Print an earley chart (list of partial parses) to stdout in a somewhat human-
readable format.
"""
function printchart(grammar, chart)
  printchart!(Base.stdout, grammar, chart)
  for (i, items) in enumerate(chart)
    println("(At token $i):")
    for item in items
      (lhs, rhs) = grammar.rules[item.rule]
      print(" [Rule $(item.rule)] $lhs ⇒ ")
      print(join(repr.(rhs[1:item.dot-1]), " "))
      print(" • ")
      print(join(repr.(rhs[item.dot:end]), " "))
      println(" (starting at $(item.start))")
    end
  end
end

"""`printparsetree(grammar, input, tree)`

Print a `ParseTree` to stdout in a somewhat readable form, with
each line corresponding to a node and indentation matching depth.
"""
function printparsetree(grammar, input, t; depth=0)
  # rule start stop
  if t.rule ≠ 0
    lhs, rhs = grammar.rules[t.rule]
    println(" "^depth * "$lhs ⇒ " * join(repr.(rhs), " ") * ", from $(t.start) to $(t.stop)")#input: $(input[t.start:t.stop])")
    for c in t.children
      printparsetree(grammar, input, c; depth=depth+1)
    end
  else
    println(" "^depth * "Terminal '$(input[t.start])' at $(t.start)")
    @assert isempty(t.children)
  end
end

end # module
