/-
Today we will see in that proofs can be understood as formal
objects in their own right. 

We will start to make our way through the valid rules of
inference from our unit on propositional logic. We will
emphasize that they are rules for combining and deriving
Boolean truth values. In predicate logic, by contrast, we
will reinterpret them as rules for combining and deriving
*proofs*. In predicate logic, the existence of a proof is
our new basis for deciding whether or not a proposition 
can be judged to be true.

In particular, we will look at how to (1) *construct* and 
(2) *use* given or assumed proofs of two simple forms of
propositions, namely conjunctions and disjunctions. 

We will see that we can view proofs as *computational*
objects. 

In particular, we will see that we can view a proof of a
conjunction, P ∧ Q, as a *pair* of proofs (a proof of P
*and* a proof of Q), and thus as a value of a *product* 
type. We will then view a proof of a disjunction, P ∨ Q,
as *either* an object constructed from a proof of P *or* 
an object built from a proof of Q, and thus a value of a 
*sum* type.  

Understanding proof construction and manipulation as
computations involving logical types (propositions) and
values (proofs) will give you the precise understanding
of deductive reasoning in predicate logic that you need
to handle a very wide variety of "prove it" problems in
the years to come, whether or not (and more likely not)
you use an automated proof assistant such as Lean or its
formalized proofs.
-/

/-
To begin we will review our polymorphic product (pair)
type. We will then see that the ∧ (and) connective in
predicate logic can be understood and formalized as a
completely analogous polymorphic *logical* type. It's
one costructor implements the and introduction rule,
and its two projection functions implement the two
and elimination rules. 
-/

namespace hidden 

-- review -- prod abstract data type!


-- be sure you fully understand this type definition
inductive prod (α β : Type) : Type
| mk (a : α) (b : β) : prod


-- here's a named example of a value of this type
def pair1 : prod nat nat := 
    prod.mk 1 1

-- by the way, we can use "example" for unnamed values
example : prod nat nat := prod.mk 1 1

-- the first, or left, projection function
-- implemented by pattern matching (aka elimination!)
def fst {α β : Type} : prod α β → α 
| (prod.mk a b) := a 

-- the second, or right, projection function
def snd {α β : Type} : prod α β → β  
| (prod.mk a b) := b 

-- and a function that from one pair derives its swap
def swap  {α β : Type} : prod α β → prod β α
| (prod.mk a b) := prod.mk b a  


/-
Our implementation of the and connective and its rules
of inference (introduction and elimination rules) in 
exactly the same way, except that our and polymorphic 
pair type now lives in "Prop," the unverse of logical
types (propositions), rather than in "Type", which as
we know is the universe of computational types.

As a reminder from propositional logic, here are three 
rules of reasoning that we showed to be semantically valid. 

def and_intro := P >> Q >> P ∧ Q
def and_elim_left := P ∧ Q >> P
def and_elim_right := P ∧ Q >> Q

In propositional logic, we read these rules as involving
truth values: e.g., if P "is true" and Q "is true" then
"P ∧ Q" "is true". We now reconceptualize these rules to
involve proofs. E.g., If we have (or assume we have) a 
proof, p, of P, and we have (or assume we have) a proof,
q, of Q, then we can construct a proof, ⟨p, q⟩, of P ∧ Q.
That's the and introduction rule. Similarly, if we have 
a proof (pair!), ⟨p, q⟩, then from it we can derive a 
proof, p, of P, and a proof, q, of Q, by nothing more
complex than projection: we destructure the pair and
return one of the other other of its two components.

-/

structure and (P Q : Prop) : Prop :=    -- Prop not Type!
intro :: (left : P) (right : Q)         -- and.intro rule

-- one poassible way to write left elimination rule
def and_elim_left {P Q : Prop} : and P Q → P
| (and.intro p q) := p

-- here's another, with elim_left in the "and" namespace
-- note that we use projection function from "structure" 
def and.elim_left {P Q : Prop}  (pq : and P Q) : P :=
pq.left 

-- and here is the right elimination rule in two forms
def and_elim_right {P Q : Prop} : and P Q → Q
| (and.intro p q) := q

def and.elim_right {P Q : Prop}  (pq : and P Q) : Q :=
pq.right


/-
A note on notation. The Lean libraries define the and
connective exactly as we've done here. In addition, the
Lean library defined ∧ as an infix notation for "and".
We won't define that notation here, so wherever we want
to use the and connective, e.g., for P ∧ Q, we'll have
to write "and P Q". Same with or. 
-/

-- tests

def pf1 : and (1=1) (eq 0 0) :=  -- 1=1 and 0=0
  and.intro (eq.refl 1) (eq.refl 0) -- proof of it!

-- We now see that pf1 is basically a pair of proofs
#reduce pf1



/- OR

We also formalize the logical connective, ∨, as an 
inductive type with two (logical) type arguments,
P and Q (two propositions). The both ∧ and ∨ take
two propositions (logical types) as arguments and
yield a larger proposition (logical type). We then
define constructors to implement the introduction
rules for the given connective. 

To build a proof of P ∧ Q, we need proofs of both
P and of Q. To build a proof of P ∨ Q it suffices
to have either a proof of P or a proof of Q. 

Here are the propositional logic rules we validated
in the last section.

def or_intro_left := P >> P ∨ Q
def or_intro_right := Q >> P ∨ Q
def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R

We now reconceptualize these rules are rules about
how *proofs* can be built and derived.
-/


#check or

inductive or (P Q : Prop) : Prop
| inl {} (p : P) : or   -- Q is implicit
| inr {} (q : Q) : or   -- P is implicit


-- example, proof of 0=0 ∨ 1=0
example : or (eq 0 0) (eq 1 0) :=
or.inl (eq.refl 0)

#check @or.elim

example : or (eq 1 0) (eq 0 0) :=
or.inr (eq.refl 0)


/-
Prove that 1=1 and 2=2.

Q: What's the form of this proposition?
A: Conjunction. Main connective is and.
Q: What rule of reasoning apply?
A: The "and" introduction and elimination rules.
Q: What is the form of the overall proof?
A: and.intro p q, where p is a proof of P and q is a proof of Q.
Q: So what remains to be done? 
A: It will now suffice to produce a proof of 1=1 and one of 2=2.
Q: How to prove 1=1? 
A: By the reflexive property of equality. 
Q: How to prove 2 =2.
A: Same way. 
QED! 
-/

-- Here it is formally

example : and (1=1) (2=2) :=
  and.intro (eq.refl 1) (eq.refl 2)


/-
The following versions of the introductions rules take two explicit
arguments each: a *proposition* for which a proof is *not* given and
a proof of the other proposition. Notice carefully the change in which
type argument is implicit in each case. Sometimes Lean can't infer 
from, say, a proof, p, of P, what disjunction, P ∨ Q, is being proved
(because it can't figure out what Q is). In such cases, you need to 
provide the Q type explicitly. These functions are useful in such cases. 
-/
def or.intro_left {P : Prop} (Q : Prop) (p : P) : or P Q :=
or.inl p

def or.intro_right (P : Prop) {Q : Prop} (q : Q) : or P Q :=
or.inr q


/-
Prove 1=0 or 1=1.

Proof: We apply the or introduction on the right rule to a
proof of 1=1. Now all that remains is to to that 1=1. This is 
by applying the reflexive property of equality (to the value,
1).
-/

-- Here is this proof formalized
example : or (1=0) (1=1) := or.intro_right (1=0) (eq.refl 1) 


/-
Prove that for any propositions, P and Q, P ∧ Q → P ∨ Q
-/



/-
NEXT UP: ∀, →, ¬ 
-/



theorem and_imp_or: ∀ { P Q : Prop}, and P Q → or P Q :=
λ (P Q : Prop) (pq : and P Q), 
    or.inl (and.left pq)


/- Still to do:

def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)
def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)
def iff_elim_left := (P ↔ Q) >> (P >> Q)
def iff_elim_right := (P ↔ Q) >> (Q >> P)
def arrow_elim := (P >> Q) >> (P >> Q)
def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)
def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)
def neg_elim := (¬ ¬ P) >> P         -- not a constructive rule
def excluded_middle := P ∨ (¬ P)     -- not a constructive rule
def neg_intro := (P >> pFalse) >> (¬ P)
def true_intro : pExp := pTrue
def false_elim := pFalse >> P
-/

end hidden