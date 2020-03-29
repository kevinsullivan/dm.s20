--import .prop_logic 
import .propositional_logic_syntax_and_semantics


open pExp


/-
Here are three propositional variables,
P, Q, and R.
-/

def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

/-
Below are 20+ formulae in propositional
logic. Your job is to classify each as
valid or not valid. To do this you will
produe a truth table for each one. It is
good that we have an automatic evaluator
as that makes the job easy. For each of
the formulae that is not valid, give an
English language counterexample: some 
scenario that shows that the formula is
not always true. 

To do this assignment, produce a truth table
for each formula. Start by defining all of
the possible interpretations for the three
propositional variables we've defined. You
can call them i_0, i_1, ... etc. Beneath
each formula, evaluate it under each of the
possible interpretations. The results will
tell you whether the formula is valid or not.
It'll also tell you under which interpretation
if any a formula is not true.
-/


def true_intro : pExp := pTrue
-- answer here

def false_elim := pFalse > P
-- answer here

def true_imp := pTrue > P
-- etc

def and_intro := P > Q > P ∧ Q
def and_elim_left := P ∧ Q > P
def and_elim_right := P ∧ Q > Q
def or_intro_left := P > (P ∨ Q)
def or_intro_right := Q > (P ∨ Q)
def or_elim := (P ∨ Q) > (P > R) > (Q > R) > R
def iff_intro :=   (P > Q) > (Q > P) > (P ↔ Q)
def iff_intro' := ((P > Q) ∧ (Q > P)) > (P ↔ Q)
def iff_elim_left := (P ↔ Q) > (P > Q)
def iff_elim_right := (P ↔ Q) > (Q > P)
def arrow_elim := (P > Q) > P > Q
def resolution := (P ∨ Q) > (¬ Q ∨ R) > (P ∨ R)
def unit_resolution := (P ∨ Q) > (¬ Q) > P
def syllogism := (P > Q) > (Q > R) > (P > R)
def modus_tollens := (P > Q) > ¬ Q > ¬ P
def neg_elim := ¬ ¬ P > P
def excluded_middle := P ∨ ¬ P
def neg_intro := (P > pFalse) > ¬ P
def affirm_consequence := (P > Q) > Q > P
def affirm_disjunct := (P ∨ Q) > P > ¬ Q
def deny_antecedent := (P > Q) > (¬ P > ¬ Q)