
-- Computational domain
#check nat
#check string
#check bool
-- "computational" types of type, Type (aka Sort 1)

-- Logical domain
#check true
#check false
#check eq 1 1   -- eq predicate applied to 1 and 2
#check 1 = 1    -- infix notation for eq
#check 3 ∈ { n : ℕ | n % 2 = 1}
#check exists (a b c : ℕ), a^2 + b^2 = c^2
-- propositions formalized as logical types: of type, Prop (Sort 0)


-- Values of computational types
#check 1
#check "hello"
#check tt
-- values of computational types are just ordinary data

-- Values of logical types (aka propositions) 
#check (eq.refl 1)
-- values of logical types are accepted as proofs


-- eq defined as polymorphic *logical* type
-- takes two values, v1 and v2, of any type, α 
-- yields a proposition, eq v1 v2, of type Prop
-- this type has just on constructor, called refl
-- takes argument, a : α, returns a value of type a=a
-- this value is accepted as a *proof* 
#print eq


-- exercises involving proofs of equality
def pf1 : 1 = 1 := _
def pf2 : "hello" = "hello" := _
lemma pf3 : 2 = nat.pred 3 := _     -- vocabulary: minor result
theorem pf4 : tt = tt := _          -- vocabulary: major result
theorem pf5 : 1 = 0 := _

def sq (n : ℕ) := n^2
#reduce (sq 3 = 9)
lemma pf6 : sq 3 = 9 := _           -- equality of reduced values
lemma pf7 : sq 5 = 25 := _



-- A logical type that has no values is false.
-- That's why the proposition, "false", in Lean is false.
-- a type with no constructors/values is said to be uninhabited
#print false
theorem pf8 : false := _


-- The proposition, "true", has one constant constructor/value/proof
#print true
theorem pf9 : true := _

/-
What we've seen so far is that some propositions are
formalized as inductive types, the values of which, as
built using available constructors, are taken to be proofs.
Indeed you can represent a wide variety of propositions
and proofs this way.
-/

inductive MaryIsASoftwareEngineer : Prop
| knowsFormalMethods
| crackProgrammer

open MaryIsASoftwareEngineer

theorem me1 : MaryIsASoftwareEngineer := knowsFormalMethods
theorem me2 : MaryIsASoftwareEngineer := crackProgrammer

/-
Lean implements a logic in which all proofs of a given
proposition are considered to be not only equally good
but actually equal. This treatment of logical values is
fundamentally different from that of computational data
values, where values built by different constructors are
*never* equal. The principle that Lean implements here 
is called the principle of "proof irrelevance." To show
that a proposition is true, you just have to exhibit *any*
proof/value of the given proposition/type. 
-/

lemma m1 : me1 = me2 := eq.refl me1


/-
Not every logical proposition or predicate is implemented
as an inductive type. In particular, proofs of ∀, →, and ¬
propositions are not elementary data values functions. 
-/

-- more to come
