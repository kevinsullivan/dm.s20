/-
Note: on this exam, you are meant to use
built-in Lean types on all problems. You
won't need to use our dm_ versions. Those
we developed just so you understand how
these types are defined and how they work.
-/

/-
1. Product types

A. Use Lean's "structure" mechanism to define an 
inductive product type, called employee, with a 
constructor, mk, that takes four arguments: 
(name : string), (id : nat), (salary : nat), 
and (active : bool).
-/

structure employee : Type :=
mk ::   (name : string) 
        (id : nat) 
        (salary : nat) 
        (active : bool)


/-
B. Define e1 to be an active employee named 
John Smith with id 123 and a salary of 50.
-/

def e1 := employee.mk "John Smith" 123 50 tt

#eval e1.salary

/-
C. Write a function called update_salary that 
takes an value of the employee type and a natural 
number representing a new salary for that employee 
and that returns a new employee object just like 
the given one but with the salary field updated 
to the given value.
-/

def update_salary : employee → ℕ → employee
| (employee.mk n i _ a) r := (employee.mk n i r a)

/-
D. Use #reduce or #eval to evaluate an expression
in which you use this function to "raise Mr. Smith's
salary to 60."
-/

#eval update_salary e1 60   -- Lean has issues here

/-
2. Sum types

Define an inductive type called rock_paper_scissors 
with three values, called "rock", "paper", and 
"scissors". Then writen a function called next, that 
takes a value of this type and returns a value of 
this type according to the following rules: given rock, 
return paper; given paper return scissors; given 
scissors, return rock.
-/

inductive rock_paper_scissors : Type
| rock : rock_paper_scissors
| paper
| scissors

open rock_paper_scissors    -- not required

def next : rock_paper_scissors → rock_paper_scissors
| rock := paper
| paper := scissors
| scissors := rock

/-
3. Inductive definitions

Define a type called nested_doll, where a value of 
this type is either "solid_doll" or "shell" applied 
to a smaller value of this same type.  Then write a 
function, depth, that takes an object of this type and 
that returns the number of shells it has. The solid 
doll has zero shells around it, of course.
-/

inductive nested_doll : Type 
| solid_doll 
| shell_doll (n : nested_doll) 

open nested_doll 

def d0 := nested_doll.solid_doll
def d1 := shell_doll d0
def d2 := shell_doll d1 
-- ad infinitum

def depth : nested_doll → ℕ 
| solid_doll := 0
| (shell_doll d) := 1 + depth d

#eval depth d2

/-
4. Polymorphic types and functions

We have represented ordered pairs as values of 
type prod S T, where S and T are type parameters.
An object of this type can be said to have two
fields, fst of type S and snd of type T. Define
an analogous type, called three_tuple S T U, 
where S, T, and U are type arguments, and where 
an object of this type has three fields, fst: S, 
snd : T, and thd : U. Then write a function,
rotate_left, that takes a value of this type and 
returns a new value of this type in which the 
field values are all rotated on position to the 
left. So, the first element becomes the third
in the result, the second becomes the first, and
the third becomes the  second. Test your function. 
-/

structure three_tuple (S T U : Type) : Type :=
mk :: (fst : S) (snd : T) (thd : U)

-- implicit args best here but not required
def rotate_left {S T U : Type}: 
    three_tuple S T U → three_tuple T U S 
| x := three_tuple.mk x.snd x.thd x.fst

-- destructuring in lieu of projection also works
def rotate_left' {S T U : Type}: 
    three_tuple S T U → three_tuple T U S 
| (three_tuple.mk s t u) := three_tuple.mk t u s

def rotate_left'' {S T U : Type} (x : three_tuple S T U) :=
match x with
| (three_tuple.mk s t u) := three_tuple.mk t u s
end

#reduce rotate_left (three_tuple.mk ff 5 tt)
#reduce rotate_left' (three_tuple.mk ff 5 tt)


/-
5. Sequences (lists) / recursion

A. Write a function, contains_zero, that takes 
a value of type "list nat" and that returns true
if any value in the list is zero and otherwise
false . An empty list has no zero values so the
function  should return false in this case. Do
not use if..then..else; use pattern matching 
within one of the cases to solve this problem.
-/

def contains_zero : list ℕ → bool
| [] := ff
| (h :: t) := match h with 
                | 0 := tt 
                | _ := contains_zero t
              end

def contains_zero'' : list ℕ → bool
| list.nil := ff
| (list.cons h t) := match h with 
                | 0 := tt 
                | _ := contains_zero t
              end

-- we'll also take this answer
def contains_zero' : list ℕ → bool
| [] := ff
| (0 :: t) := tt 
| (_ :: t) := contains_zero t
    
-- This answer show Lean's list notations 

/-
B. Write a function, inc_values, that takes a 
value of type "list nat" and that returns a 
list just like the given one but which each value 
incremented by one. So for example, given a list, 
[1, 2, 3], inc_values will return [2, 3, 4]. 
-/

def inc_values : list ℕ → list ℕ 
| [] := []
| (h :: t) := ((h + 1) :: (inc_values t))

/-
inc_values [1, 2, 3]
2 :: (inc_values [2, 3])
2 :: (3 :: (inc_values [3]))
2 :: 3 :: 4 :: inc_values []
2 :: 3 :: 4 :: nil
[2, 3, 4]
-/

#eval inc_values [1, 2, 3]

/- 
6. Binary trees / recursion

A. Define a type called binary_tree_nat. Its values
will represent binary trees of natural numbers. Such 
a tree is either "empty" or it is a "node" containing
a natural number and two smaller binary_tree_nat values.
-/

inductive binary_tree_nat : Type
| empty
| node  (n : ℕ) 
        (left : binary_tree_nat) 
        (right : binary_tree_nat)

/-
B. Then define a function that takes a binary_tree_nat 
value as an argument and that returns the sum of all of 
the natural numbers in the tree. An empty tree contains
no natural numbers, so the result must be zero in this
case.
-/

def tree_sum : binary_tree_nat → ℕ 
| binary_tree_nat.empty := 0
| (binary_tree_nat.node n l r) := n + tree_sum l + tree_sum r

/-
7. Partial functions.

A partial function is a function that is not defined 
for all values of its argument type. Yet all function 
definitions in Lean must be total. To represent a 
partial function as a total funtion in Lean, we use the
option type. We define a function that always returns 
an option, and so is total, but the result is in one 
of two forms: either "some result" when the result of
the underlying partial function is defined, or "none"
when it's not.

We have implemented a predecessor function, pred : ℕ → ℕ,  
that's a little "funky": when applied to zero, it returns
zero, even though it could be argued that the predecessor
of zero (in the natural numbers) should be defined to be
undefined. 

Implement a version of pred, let's call it pred_partial, 
that for any non-zero argument, n, returns "some result" 
where "result" is the predecessor of n, but that when 
applied to zero returns "none", to flag that the function
is not defined for zero. Write the function pred_partial
and test it for zero and non-zero argument values.
-/

def pred_partial : ℕ → option ℕ 
| 0 := none
| (nat.succ n') := some n'