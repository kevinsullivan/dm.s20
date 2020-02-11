# The option type

## Purpose: represent partial functions

All functions in Lean must be total, but some
functions in mathematics are partial, which is
to say, they are undefined for some values of
their arguments. For example, division is not
defined when the denominator, y, in x / y, is
zero.

## Trick is always to return an option value

The option type allows us to represent missing
or undefined values of some other type. To this
end, it has two constructors. The first takes
no arguments and represents and undefined value
of a given type. The second takes a value of a
given type and simply represents that value.

We can represent sucn partial math functions
as total functions that _always_ return a value
of type option, but that return option.none in
cases where the math function being implemented
is undefined, and that return (option.some a) in
cases where the function is defined and a is the
result.

## New (for us) type definition concepts

The option type presents a new combination of
features for: it's both polymorphic, so that
we can represent possibly undefined values of
any type; and it's a sum, or variant type, in
that it has multiple constructors, none and
some.

## A new type inference detail

The constructors of a polymorphic type are
polymorphic. When the type arguments to such
constructors can be inferred, type arguments
are implicit. This is the case for the some
constructor, since it takes an argument from
which the type can always be inferred.

The none constructor by constrast takes no
arguments, and so requires an explicit type
argument. In some situations, however, the
type argument can be inferred (as we will
see). Nevertheless, explicit arguments must
be provided. The way to tell Lean to infer
type arguments in such situations is to put
a {} after the name of the constructor. This
is the preferred style of defining types in
Lean that are polymorphic but that have
constructors with no arguments.
