"""`Match`

This submodule contains several datatypes that represent certain classes of
tokens. Using these datatypes in the grammar instead of enumerating symbols is
convenient for all but the most basic grammars.

The following datatypes for unicode characters are available:

* `ASCII` - matches ASCII characters
* `Space` - matches Unicode whitespace
* `Digit` - matches a decimal digit (0 through 9)
* `HexDigit` - matches a hexadecimal digit (0 through 9 and 'a' through 'f')
* `Letter` - matches a Unicode letter
* `Lower` - matches a Unicode lower case character
* `Upper` - matches a Unicode upper case character
* `Print` - matches a Unicode printable character

Moreover, the following datatypes are available for all types of tokens:

* `AnyToken` - matches any token regardless of type or value
* `OneOf` - matches a token (class) from a predefined list
* `Predicate` - matches a token if that token fulfills a given predicate
"""
module Match

export OneOf
export ASCII, Space, Digit, Letter, Lower, Upper, Print, AnyToken
export matches

"""`matches(class, token)`

Returns true if `token` belongs to the given `class` of tokens. The default
implementation compares equality, i.e.
`matches(class, token) = token == class`.

For context, see also: `recognize`, `parse`. For a list of predefined token
classes, see `Match`.
"""
function matches(a, b)
  a == b
end

"""`OneOf(alternatives)`

Creates a token class that matches any one of the given alternatives. For
more information see `matches`.
"""
struct OneOf{T}
  alternatives :: Vector{T}
  OneOf(as) = OneOf(collect(as))
  OneOf(as :: Vector) = new{eltype(as)}(as)
end

function matches(as :: OneOf, b)
  any(a -> matches(a, b), as.alternatives)
end

"""`ASCII()`

Creates a token class that matches any ASCII character.
"""
struct ASCII end

matches(_ :: ASCII, token) = isascii(token)

"""`Space()`

Creates a token class that matches any whitespace token (i.e. one for which
`isspace` returns true).
"""
struct Space end

matches(_ :: Space, token) = isspace(token)

"""`Digit()`

Creates a token class that matches the digits '0' through '9'.
"""
struct Digit end

matches(_ :: Digit, token) = isdigit(token)

"""`Letter()`

Creates a token class that matches a unicode letter.
"""
struct Letter end

matches(_ :: Letter, token) = isletter(token)

"""`Lower()`

Creates a token class that matches a lower-case unicode letter.
"""
struct Lower end

matches(_ :: Lower, token) = islowercase(token)

"""`Upper()`

Creates a token class that matches an upper-case unicode letter.
"""
struct Upper end

matches(_ :: Upper, token) = isuppercase(token)

"""`Print()`

Creates a token class that matches a printable letter (including whitespace).
"""
struct Print end

matches(_ :: Print, token) = isprint(token)

"""`HexDigit()`

Creates a token class that matches a hexadecimal digit, i.e. the digits '0'
through '9' or latin letters 'a' through 'f' (in upper and lower case
variants).
"""
struct HexDigit end

matches(_ :: HexDigit, token) = isxdigit(token)

"""`AnyToken`

Creates a token class that matches any token.
"""
struct AnyToken end

matches(_ :: AnyToken, _) = true

"""`Predicate(p)`

Creates a token class that matches any token for which the given predicate `p`
is true.
"""
struct Predicate{P}
  p :: P
end

matches(pred :: Predicate, t) = pred.p(t)

end # Match
