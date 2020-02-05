namespace hidden


-- Sum type: one of these or one of those
-- Product type: one of these and one of those

inductive prod_nat_nat : Type
| mk : ℕ → ℕ → prod_nat_nat 
--| mk (x y : ℕ) : prod_nat_nat

def p1 := prod_nat_nat.mk 2 3
def p2 := prod_nat_nat.mk 5 0

def fst_prod_nat_nat : prod_nat_nat → nat :=
λ p,
    match p with 
    | (prod_nat_nat.mk a b) := a
    end

def snd_prod_nat_nat : prod_nat_nat → nat :=
λ p,
    match p with 
    | (prod_nat_nat.mk a b) := b
    end

def snd_prod_nat_nat' : prod_nat_nat → nat 
    | (prod_nat_nat.mk a b) := b

def snd_prod_nat_nat'' (p : prod_nat_nat) : nat := 
    match p with 
    | (prod_nat_nat.mk a b) := b
    end

-- Testing
#eval fst_prod_nat_nat p1
#eval snd_prod_nat_nat p1
#eval fst_prod_nat_nat p2
#eval snd_prod_nat_nat p2

/-
Syntax with field names and projection 
functions for special case of product type. 
We call such objects structures, or records.
We call their elements fields, and the names 
are called field names.
-/

structure prod_nat_nat' : Type :=
mk :: (x y : ℕ) 

def p3 := prod_nat_nat'.mk 2 3
def p4 := prod_nat_nat'.mk 5 0

#eval p3.x
#eval p3.y
#eval p4.x
#eval p4.y

/-

How does this compare with classes in Java?
Correct: OOP doesn't so readily support sum
types. There are "design patterns" that you
can use, but they're rather indirect ways 
of expressing a very basic idea: an object
can be of this form *or* of that form. It
also goes without saying that OOP languages
such as Java and Pyton don't support case
analysis / pattern matching / destructuring
like functional languages do.
-/

-- Challenge problem

/-
Define this function so that applying it
to any pair returns the pair with its first
and second elements swapped.
-/
def swap_prod_nat_nat : prod_nat_nat → prod_nat_nat := _

/-
How would you write this kind of code in Java
or another ordinary imperative language? Yes: 
You have to use a temporary variable (unless 
the language supports multiple assignment).
-/

end hidden