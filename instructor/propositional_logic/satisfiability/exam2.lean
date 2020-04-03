import .satisfiability
import .rules_of_reasoning

/-
CS2102 Exam #2: Propositional Logic
-/

/-
#1. Define a predicate function, is_satisfiable: pExp → bool
that returns true iff the given proposition is satisfiable.
Hint: Model your answer on our definition of is_valid. You
may need to define one or more helper functions. You should
test your solution, but we will only grade your definition.
Please write test cases in a separate file. Do not submit
that file.
-/

-- Answer here



/-
#2. Clearly the propositions in rules_of_reasoning.lean that
are valid are also satisfiable. But what about the following?
Apply your satisfiability predicate function to decide whether
or not each of the following formulae is satisfiable or not.
Write an "#eval is_satisfiable e" command for each expression.


A. The "fallacies" in that file (the ones that aren't valid).

B. The proposition, pFalse.

C. The following propositions:

1. P ∧ ¬ P
2. P ∨ ¬ P
3. = (¬x1 ∨ x2) ∧ (¬x2 ∨ x3 ∨ ¬x4) ∧ (x1 ∨ x2 ∨ x3 ∨ ¬x4)

Note that for 3. you will have to define four new variables.
Call them x1, x2, x3, and x4.
-/

-- Answers here




/-
3. In the previous problems, you defined a satisfiability
predicate function that returns true or false depending on
whether a given formula is satisfiable or not. Often we will
want to know not only whether there exists a solution but an
actual example of a solution, if there is one. Define a function
called sat_solver : pExp → option (var → bool) that returns a
satisfying interpretation (as "some interpretation") if there
is one, or "none" otherwise. Hint: Model your solution on our
validity checker. First compute the list of interpretations for
a given expression, e, then reduce that list to a value of type
option (var → bool). Evaluate e under each interpretation in 
the list until either (A) you find one, call it i, for which e
evaluates to true, or until you reach the empty list, empty
handed. 
-/

-- Answer here




/-
4. Define a predicate function, is_unsatisfiable : pExp → bool,
that takes a propositional logic formula, e, and returns true
iff e is unsatisfiable. Hint: Easy. Build on what you have.
-/

-- Answer here




/-
5. Given a propositional logic expression, e, and an incorrect
claim that it's valid, we often want to produce a counter-example
to that claim. Such a counter example is an interpretation under
which the expression is not true. Equivalently, a counterexample
is an interpretation under which the *negation* of the expression
*is* true. 

Define a function, counterexample : pExp → option (var → bool),
that takes any expression e and returns either a counterexample
(as "some interpretation") or "none" if there isn't one. Hint:
given e, try to find a model for the expression, ¬ e.
-/

-- Answer here




/-
6. Give an English language example for every valid rule of
reasoning in rules_of_reasoning.lean, and also give an English
language counter-example for each fallacy.

For example, for the rule, P >> Q >> P ∧ Q, you could say,
"If the ball is red then if (in addition to that) the box
is blue, then (in this context) the ball is red AND the box
is blue." It will be easiest is you re-use the same words
for P, Q, and R, in all of your examples. E.g., P means "the
ball is red", Q means "the box is blue", etc.

Copy the contents of rules_of_reasoning.lean into this comment
block and under each rule give your English language sentence.
-/