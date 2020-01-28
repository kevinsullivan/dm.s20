/-
Identifiers are names that can be bound to
terms. Having bound an identifier to a term,
one can use the identifier instead of writing
out the whole term in subsequent expressions.

When we bind an identifier to a term, we say
that we have created a definition for that
identifier. It is defined to have the term as
its value.

In Lean, we use the keyword, _def_, to create
such a definition. The syntax is _def_, then
the identifier name, then a _:=_, and then 
the term to be bound to the identifier. For
example, to bind the identifier (name), 
$z$, to the value, $nat.zero$, we'd write 
the following _definition_ in Lean.

```
def z := nat.zero
```

<Practice 
text=`Using Lean, define $n$ to be
bound to the natural number, $0$; $s$ to be
bound to the string, _I love logic; and $b$
to be bound to the Boolean value, $tt$.`/>


Having done that, if we then evaluate the
_identifier expression_, $z$, it evalutes
to $nat.zero$.

## Comparison with Imperative Languages.

A variable in an _imperative language_,
such as Java, Python, C, C++, or Basic,
represents a location in an updatable,
or _mutable_ memory. Values can be read
from a memory, and values can be stored
into a memory. Storing a value into a
memory erases and overwrites the value
that was previously there.

Consider this fragment of a Java program.

```java
int j;
j = 1;
j = j + 1;
```

After the first line, j has no value and
an attempt to use j will lead the compiler
to issue an error. After the second line, 
the value stored in the memory location
named by j is 1. In the third line, the 
value, 1, is read from j; 1 is added to
it; and this value is then stored as the  
new value of (in the memory named by) j.

## Imperative Languages 

Languages, such as Java, Python, C, and 
C++ are based on _commands_, and are thus
said to be_imperative_. The commands in our
example are commands to update specific
locations in _memory_ with new values.

At the heart of such a language is always 
a _mutable store_, or _memory_, that can be
changed, or _mutated_, by commands such as
_assignment_ commands.

## Functional Languages

A _functional_ language, by contrast, has no
concept of a mutable store. Such a language
is not one of commands that update the state
of a memory, but of mere _expressions_ that
can be evaluated to produce a value. As in
arithmentic, expressions can be evaluated, 
but evaluating them doesn't produce and side
effects (such as changes in the values in a 
memory or the turning on of some electrical
switch) anywhere else in the world.

For example, evaluating the expression
$3 + 2$ yields the value $5$, but does
not cause changes to a memory. Evaluating
expressions is said to be pure, or free of
_side effects_. 

## Identifiers and Bindings

This brings us finally to the notion of
_identifiers_ in functional languages. 
An identifier is simply a name for some
other term. For example, we might bind 
the identifier, $n$, as a name, to the 
term, $nat.zero$. Henceforth we could
write $n$ instead of $nat.zero$. It is
easier to read and write $n$ than to 
read or write $nat.zero$. 

Furthermore, once bound to one term, an
identifier cannot be bound to another
term. The values of identifiers in most
functional languages are thus said to be
_immutable_.

## Evaluation of Identifier Expressions

And so now we can talk about evaluation
of _identifier expressions_. To evaluate
an identifier expression, Lean in effect
finds the term bound as the value of the
identifier, then evaluates that term to
produce the final result of evaluating the  identifier expression. 

For example, if the identifier, $x$, is bound to the term, $1 + 2$, then evaluating the expression, $x$, will return the result
of evaluating the expression, $1 + 2$, that
is bound to $x$, producing a result of $3$.
-/

def x := 1 + 2
#print x
#eval x

/-
Identifiers, bindings, types
-/

def b' : bool := (tt : bool)
def b'' := tt

-- type inference

def s' : string := "I love logic!"

def n' : ℕ := 1

/-
Functions and their application
-/

#eval band tt tt
#eval tt && tt

#eval nat.add 3 4

#eval string.append "Hello, " "Logic!"
#eval "Hello, " ++ "Logic!"

#check band



/-
Types
-/

/-
Every term has exactly one type
A type defines a set of terms
These sets are disjoint
-/

#check 0
#check "Hello"
#check tt
#check prod.mk 2 "Hi!"
#check true     -- a proposition

#check bool
#check string
#check ℕ 

#check Type 0
#check Type 1

#check Prop
#check Sort 0
#check Sort 1
#check Sort 2

