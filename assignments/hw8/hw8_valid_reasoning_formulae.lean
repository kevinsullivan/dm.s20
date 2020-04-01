import .propositional_logic_syntax_and_semantics

open pExp

/-
Your task: We give you propositions in zero to 
three variables (P, Q, and, R). You must decide
whether each is valid or not. To do this, you
must use pEval to evaluate any given propositions
under each of the possible interpretations of its
variables. 

To test a 1-variable proposition will require
two interpretations; for 2 variables, four; for
three, eight, etc. In general, there are 2^n,
where n is the number of variables. Adding one
variable geometrically increases the number of
possible interpretations.
-/

/-
Here are the three propositional variables, P
Q, and R that we'll use to write propositions 
and test them here. 
-/

def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)



/-
Below is a list of formulae, many of which
express fundamental rules of valid reasoning.
We also state several fallacies: desceptively
faulty, which is to say invalid, non-rules of
logically sound reasoning.  

Your job is to classify each as valid or not 
valid. To do this you will produe a truth 
table for each one. It is good that we have 
an automatic evaluator as that makes the job 
easy. For each of the formulae that's not valid, 
give an English language counterexample: some 
scenario that shows that the formula is
not always true. 

To do this assignment, evaluate each proposition
under each of its possible interpretations. Each
interpretation defines the inputs in one row of
the truth table, and the result of applying pEval
to the expression under that interpetation, gives
you the truth value of the proposition under that
interpretation. 

A given proposition will be valid if it evalutes
to true under *all* of its interpretations. You
have to define some interpretations, then apply 
the pEval function to the given proposition for
each of its possible interpretation.axioms

Some of the formulae contain only one variable.
We use P. You will need two interpretations in 
this cases. Call them Pt and Pf. A one-variable
propositions has two interpretations, and thus
two rows in its truth table.

Some formula have two variables. We call them
P and Q. Now there are four interpretations. Call 
them PtQt, PtQf, PfQt, PfQf. 

Finally, some of the propositions we give you have 
three variables. Here we have eight interpretations
under which to evaluate each such proposition. You
can give them names such as PtQtRt, PtQtRf, etc. 

If we look at the sequence of t's and f's in each
of these names and rewrite t's as ones f's as zeros, 
then we see that our names basically count down from
2^n-1 to zero in binary notation.  

PQR
ttt 111 7   2^3-1
ttf 110 6
tft 101 5
tff 100 4
ftt 011 3
ftf 010 2
fft 001 1
fff 000 0   

So, for each proposition, evaluate it under each
of its possible interpretations; then look at the
list of resulting truth values. If all are true,
then you have proved that the proposition is valid.
If there is at least one interpretation under which
the proposition evaluates to true, it's decidable.
If there is no interpretation that makes it true,
then it is unsatisfiable.
-/

/- # 1. 

Define three sets of interpretations, one for each 
"arity" of proposition (1-, 2-, or 3 variables), as
explained above.
-/

-- Answer


/-
2. Use pEval to evaluate each of the following formulae
under each of its possible interpretations. The use the
resulting list of Boolean truth values to decide which
properties the proposition has. Here are the propositions
for which you are to decide the properties it has.
-/

def true_intro : pExp := pTrue

def false_elim := pFalse >> P

def true_imp := pTrue >> P

def and_intro := P >> Q >> (P ∧ Q)

def and_elim_left := (P ∧ Q) >> P

def and_elim_right := (P ∧ Q) >> Q

def or_intro_left := P >> (P ∨ Q)

def or_intro_right := Q >> (P ∨ Q)

def or_elim := (P ∨ Q) >> (P >> R) >> (Q >> R) >> R

def iff_intro :=   (P >> Q) >> (Q >> P) >> (P ↔ Q)

def iff_intro' := ((P >> Q) ∧ (Q >> P)) >> (P ↔ Q)

def iff_elim_left := (P ↔ Q) >> (P >> Q)

def iff_elim_right := (P ↔ Q) >> (Q >> P)

def arrow_elim := (P >> Q) >> (P >> Q)

def resolution := (P ∨ Q) >> (¬ Q ∨ R) >> (P ∨ R)

def unit_resolution := (P ∨ Q) >> ((¬ Q) >> P)

def syllogism := (P >> Q) >> (Q >> R) >> (P >> R)

def modus_tollens := (P >> Q) >> (¬ Q >> ¬ P)

def neg_elim := (¬ ¬ P) >> P

def excluded_middle := P ∨ (¬ P)

def neg_intro := (P >> pFalse) >> (¬ P)

def affirm_consequence := (P >> Q) >> (Q >> P)

def affirm_disjunct := (P ∨ Q) >> (P >> ¬ Q)

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)

/-
Study the valid rules and learn their names. 
These rules, which, here, we are validating 
"semantically" (by the method of truth tables)
will become fundamental "rules of inference",
for reasoning "syntactically" when we get to 
predicate logic. There is not much memorizing
in this class, but this is one case where you
will find it important to learn the names and
definitions of these rules.
-/