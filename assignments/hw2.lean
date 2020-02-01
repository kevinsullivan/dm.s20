/-
UVa CS2102/Sullivan, Spring 2020, Homework #2

This homework assignment is due by noon on Tuesday, 
Feb 4. Submit your result through the HW#2 tab under
the Assignments category on Collab. Do so by uploading
a completed version of this file.

The goal of this assignment is to develop and evaluate 
your ability to write simple abstract data types in Lean,
comprising both inductive data definitions and definitions
of functions, in several syntactic styles, that operate 
on values of such types. 
-/

/- [49 points]

#1. In the space after this comment, first define a data 
type, dm_bool, as we did in class, with values dm_tt and
dm_ff. We will take the values of this type to represent
the Boolean algebra truth values, true and false. Then
define functions operating on values of type dm_bool that 
implement the Boolean functions, not, and, or, nand, xor, 
implies, an equiv (iff). 

Note: The heads-up announcement of a few days ago mis-stated
the types of these operations as involving values of type
bool. You must use dm_bool throughout. The point is that you
are now seeing how to specify/implement Boolean algebra, not
just to use Boolean algebra functions built in to a language.

Precede each of your function definitions with a comment
presenting the "truth table" for the function to be 
defined. Then *after* each function definition, use Lean's 
#eval or #reduce command to test it for all possible 
combinations of argument values. For example, you should
have four test cases for each binary function, for each of
the four combinations of two Boolean values. You may use 
resources  such as Wikipedia to learn the truth tables for
each of these functions if you don't already know them. 
-/


-- Answers here

/- [51 points]

#2. In a separate file called months.lean, define a new
abstract data type. It will define a data type, months,
the values of which are the names of the months. Use all
lower case names for months, e.g., january. 
-/

-- Answer here

/-
Complete your "month" ADT definition with definitions of
two functions, next_month and is_winter_month, as follows.
However, to practice writing functions in different ways,
write each of the two functions in each of the following
styles, adding "prime" marks to the function names so as 
to avoid naming conflicts:

- lambda expression (with a match/with expression)
- C-style (with a match/with expression)
- by cases (no explicit match/with expression needed)

-/

/-
A. Given a month as an argument, return the next month in
the sequence of months of the year. E.g., the function 
application, (next_month december), will return january. 
-/


-- Answer here


/-
B. Given a month as an argument, return the dm_bool 
value, dm_tt (representing "true"), if the given month
is a winter month (december, january, or february), 
and dm_ff otherwise. Do not use more than four pattern
matching rules.
-/
