
/-
A polymorphic type, poly, with one type
parameter, here named alpha. The fact that
we use a Greek letter has no significance
other than being a convention in Lean.
-/
inductive my_prod (α : Type) : Type
| mk : α → α → my_prod

def p1 := my_prod.mk 3 5

def swap (α : Type) : my_prod α → my_prod α
| (my_prod.mk x y) := my_prod.mk y x

def p2 := swap ℕ p1 -- explicit type argument

def swap' {α : Type} : my_prod α → my_prod α
| (my_prod.mk x y) := my_prod.mk y x

/-
This version uses curly braces around the
declaration of the type argument, α. What
this tells Lean is that it should not expect
an explicit type parameter, rather it should
use type inference to infer the value of this
parameter automatically (from the value to
which the funtion is applied).
-/

-- It works!

def p3 := swap' p1  -- type argument implicit

/-
In summary, when you want the programmer to be
able to apply a polymorphic functions without 
explicitly giving type arguments, enclose the 
declarations of the arguments in curly braces 
and then do not give these arguments when the functions are applied. If for some reason you
have to give such arguments explicitly, prefix
the call with @.
-/

def p4 := @swap' ℕ p1

