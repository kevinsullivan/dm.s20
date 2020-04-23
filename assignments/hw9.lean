/-
HOMEWORK #9 

There is no need to import our previous definitions.
For this homework you will just use Lean's built-in
notations and definitions. 
-/

/-
Prove the following. Note that you can read each of 
the propositions to be proved as either a logical
statement or as simply a function definition. Use
what you already know about the latter to arrive
at a proof, and then understand the proof as one
that shows that the logical statement is true.
-/

theorem t1 {P Q : Prop} (p2q : P → Q) (p : P) : Q :=
  _


theorem t2 {P Q R : Prop} (p2q : P → Q) (q2r : Q → R): P → R :=
  _

/-
Use "example" to state and prove the preceding two 
theorems but using "cases" style notation rather
than C-style. Remember, "example" is a way to state
a proposition/type and give an example of a value.
Here's an example of the use of "example". Give
your answers following this example.
-/

-- example
example : ℕ := 5

-- Your two answers here




/-
Now give English-language versions of your two proofs.
-/


/-
Prove the following using case analysis on one
of the arguments (i.e., use match...with...end
at a key point in your proof). Use "cases" style
notation. 
-/

theorem t3 : ∀ (P : Prop), false → P
| P f := _


/-
Prove false → true by applying t3 to a proposition.
You have to figure out which one.
-/
theorem t4 : false → true := t3 _

/-
Define t5 to be the same as t3 but with P taken as
an implicit argument.
-/

theorem t5 : ∀ {P : Prop}, false → P
| P f := _


/-
Define t6 to be a proof of false → true by
applying t5 to the right argument(s). 
-/

theorem t6 : false → true := _

/-
That is almost magic. In English, t3 proves 
that false implies *any* proposition, so just
*apply* t3 to *true* in particular, but use t5 
instead of t3.

What you see here is really important: Once 
we've proved a general theorem (a ∀ proposition)
we can *apply the proof* to any *particular* case 
to yield a proof for that specific case. This is 
the elimination rule for ∀. It is also known as
universal instantiation (UI). 
-/


/-
Next we see the idea that test cases are really
just equality propositions to be proved. Here, 
for example, is a definition of the factorial
function.
-/

def fac : ℕ → ℕ 
| 0 := 1
| (n' + 1) := (n' + 1) * fac n'

/-
Use "example" to write test cases for the
first ten natural number arguments to this
function.
-/

example : fac 0 = 1 := eq.refl 1
example : fac 1 = 1 := eq.refl _  -- Inferred
example : fac 2 = 2 := rfl        -- Shorthand
#check @rfl           -- infers type and value


-- The rest of your answers here

/-
Insight: A test case is an equality proposition.
It is proved by "running" the program under test
to reduce the application of the function to input
arguments to produce an output that is then asserted
to be equal to an expected output. 

In many cases, all we have to do is to simplify
the expressions on each side of the eq to see if
they reduce to exactly the same value. If so, we
can *apply* eq.refl (a universal generalization!)
to that value. Using rfl we can avoid even having
to type that value in cases where Lean can infer
it.
-/


/-
The next problem requires thave you give a proof of 
a bi-implication, a proposition whose connective is 
↔. To prove a bi-implication requires that one prove
an implication in each direction. 

Here you are asked to prove P ∧ Q ↔ Q ∧ P. What this
formula asserts is that ∧ is commutative. To construct
a proof of this proposition you will have to apply 
iff.intro to two smaller proofs, one of P → Q and 
and of Q → P. 

Start by "assuming" that P and Q are arbitary but 
specific propositions (∀ introduction), then apply 
iff.intro to two "stubbed out" arguments (underscores). 
We suggest that you put the underscores in parentheses 
on different lines. Then recursively fill in each of
these stubs with the required types of proofs. Study
the context that Lean shows you in its Messages panel
to see what you have to work with at each point in 
your proof constructions.
-/
theorem t7 : ∀ {P Q : Prop}, P ∧ Q ↔ Q ∧ P :=
_


/-
In English, when asked to prove P ↔ Q, one says, "it
will suffice to show P → Q and then to show Q → P." One
then goes on to give a proof of each implication. It
then follows from iff.intro that a proof of P ↔ Q can
be constructed, proving the bi-implication.
-/


/-
The trick here is to do case analysis on porq
(use match ... with ... end) and to show that 
a proof of R can be constructed *in either case*.
-/
theorem t8 {P Q R : Prop} (p2r : P → R) (q2r : Q → R) (porq : P ∨ Q) : R := _



/-
We suggest that you use  "let ... in" to give
names to intermediate results that you then combine
in a final expression to finish the proof.
-/
theorem t9 : ∀ (P Q: Prop), (P → Q) → ¬ (P ∧ ¬ Q) :=
_



theorem neg_elim' : ∀ (P : Prop), ¬ ¬ P → P :=
λ P,
λ nnp,
_           -- STUCK!!


theorem neg_elim : ∀ (P : Prop), (P ∨ ¬ P) → (¬ ¬ P → P):= 
λ P,
    λ h, 
        λ nnp,
            match h with
            | or.inl p := p
            | or.inr np := false.elim (nnp np)  -- false elimination
            end

-- nnp : (¬ P) → false
-- np : ¬ P
-- nnp np = false!

-- Let's use H to mean There is a sub-exponential time algorithm for Boolean sat.
-- ¬ H means that there's not one.
-- H ∨ ¬H

-- make Lean into a classical logic
-- axiom em : ∀ (P : Prop), P ∨ ¬ P
#check classical.em




theorem t10 : ∀ (P : Prop), P ∨ ¬ P :=
_


#check @or.inl
#check @or.inr

theorem t11 : ∀ (P Q : Prop), ¬ (P ∨ Q) ↔ ¬ P ∧ ¬ Q :=
λ P Q, 
    iff.intro 
        (λ not_porq,
            match (classical.em P) with
            | or.inl p := false.elim (not_porq (or.inl p))
            | or.inr np := match (classical.em Q) with
                           | or.inl q := false.elim (not_porq (or.inr q))
                           | or.inr nq := and.intro np nq
                           end
            end    
        )
        _


theorem t12 : ∀ (P Q : Prop), ¬ (P ∧ Q) ↔ ¬ P ∨ ¬ Q :=
_

/-
For the following exercises, we assume that there is 
a type called Person and a binary relation, Likes, on
pairs of people.
-/
axiom Person : Type
axiom Likes : Person → Person → Prop


/-
Prove the following
-/
theorem t13 : 
  (∃ (p : Person), ∀ (q : Person), Likes q p) → 
  (∀ (p : Person), ∃ (q : Person), Likes p q) :=
λ h, 
    match h with
    | exists.intro p pf := 
        λ q, 
            (exists.intro p (pf q))
    end


