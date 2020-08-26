/-
Proof strategies.

- DIRECT PROOF: from established facts

- BY NEGATION: to prove ¬ P, assume P;
  show that this yields a contradiction.
  From this a proof of false can then 
  be derived. This shows P → false. And
  that is the definition of ¬P.

  Example: Prove that the square root of
  two is irrational.

  It sounds like we're trying to prove P,
  where P := "sqrt(2) is irrational". But
  it's better to take P to be the proposition
  that "sqrt(2) is rational", and to view
  the goal as to prove ¬ P.

  Prove that the square root two is NOT
  rational.

  Prove "¬ sqrt(2) is rational".

  Proof: BY NEGATION. assume sqrt(2) is 
  rational. In this case, we can write
  sqrt(2) as some fraction, a/b (for that
  is what it means for a number to be 
  rational). We now want to show that
  this leads to a contradiction so that
  we can conclude that our assumption is
  false, thus ¬ P is true. Details left
  as an exercise.



  - BY CONTRADICTION : to prove P, assume
    ¬ P and show that this leads to a
    contradiction, from which a proof of
    false can be derived. This proves
    ¬ P → false, which is equivalent to
    ¬ ¬ P. The apply the *classical* rule
    of negation elimination to deduce P.

    Classical rule of negation elimination:
    ∀ (P : Prop), ¬ ¬ P → P.

    Prove 0 = 0 by contradiction.

    We want to prove P (0 = 0). Assume
    ¬ (0 = 0), and show that this leads
    to a contradiction. But by the
    reflexive property of equality, which
    says everything is equal to itself, 
    we know immediate that 0 = 0. That
    gives us a direct contradiction, 
    between ¬ (0=0) and (0=0). From
    such a contradiction we can derive
    a proof of false, showing that
    ¬ (0=0) → false. And this just means
    ¬ (¬ 0=0). The by classical negation
    elimination, this implies 0 = 0.

    BY CASE ANALYSIS. Show that for any
    possible form that an assumed value
    can take (e.g., nat.zero or nat.succ
    n' for some n'), i.e., for each of 
    its possible constructors, that the
    goal must be true. Then in must be 
    true in ALL cases, which proves that
    it is valid.

    - Today: proof BY INDUCTION.
-/

-- Answer to question about why contradictions imply false
axiom P : Prop
axiom p : P
axiom np : ¬ P  /- P → false -/
#check (np p)

/-
Prove this: ∀ (m : ℕ), my_add 0 m = m
-/

def my_add : ℕ → ℕ → ℕ 
| nat.zero m := m
| (nat.succ n') m := nat.succ (my_add n' m)

-- 0 + m = m
-- (1 + n') + m = 1 + (n' + m)

/-
Proof: By the definition of addition,
and specifically by the first of the
two cases, which tells us that for any
m, 0 + m = m. 
-/


/-
Many proofs are accomplished by mere
simplification of both sides of some
equation *using function definitions*
that are already known. 
-/

/-
If one is being precise, however, there
are some unexpected consequences. One is
that sometimes something that looks easy
turns out to be a bit more complicated.

For example, try to prove this (using)
only what we know so far.
-/

example : ∀ (n : ℕ), my_add n 0 = n := _

/-
We have no rule (yet) for adding zero 
on the right, so simplifying using the
definition of my_add doesn't work.
Instead, we need to try a whole different
proof strategy.
-/

/-
Here's the idea: 

- every inductively defined type has a
  corresponding induction rule, which  is
  a rule for showing that some predicate
  is true for *every* value of that type

- Here's induction principle for the ℕ type:
  ∀ P : (ℕ → Prop),
  P 0 → 
  ((∀ n' : ℕ), P n' → P (nat.succ n')) → 
  ∀ n, P n

In other words, for any property of natural
numbers (a predicate that takes a natural
number as an argument), *if* 0 satisfies 
the predicate and whenever any n' satisfies
it, so does n'+1, then the predicate is
true/satisfied by *all* natural numbers.

Think of the a proof of (P 0) as "showing that
the first domino falls", and (P n' → P (n' + 1))
as showing that "whenever *any* domino falls, so
does the next one."" Together these proofs show
that all the dominos fall. 

[THIS IS THE KEY THING TO REMEMBER: The
induction principle. Mathematical induction
is nothing but the induction principle for
ℕ. There is a corresponding induction rule
for every inductively defined type.]

In other words, for any predicate/property
P, to show that ∀ (n : ℕ), P n, it suffices 
to show the following: 
    (1) P 0, 
    (2) (∀ n' : ℕ), P n' → P (nat.succ n')
-/

/-
The next key idea in a proof by induction 
is that when proving (2), you get to *assume*
that P holds for some arbitrary n' and all you
have to do is to show that in this context it
must also hold for n'+1.
-/

/-
Example: We want to prove ∀ n, n + 0 = n.
Proof by induction. If suffices to show that
(1) Case: n = 0. We need to show 0 + 0 = 0. 
    This is trivially proved by applying the first rule of my_add.
    So we have now proved (P 0).
(2) Case: n = nat.succ n': 
    Show P n' → P (nat.succ n').
    In other words, show n'+ 0 =n' → (n' + 1) + 0 = (n' +1). 
    Assume P n'? I.e., assume that: my_add n' 0 = n'
    Now show P (nat.succ n'): that my_add (nat.succ n') 0 = (nat.succ n').
    *** simplify: my_add (nat.succ n' 0) = 
                  nat.succ (my_add n' 0) = --2nd rule of my_add
    *** apply induction hypothesis, that my_add n' 0 = n'.
    Now we have my_add (nat.succ n' 0) = nat.succ n'.
    We have thus now proved (2), that P n' → P (nat.succ n').
    Applying the induction principle to these proofs yields a proof
    of ∀ n, n + 0 = n.
    QED.

def my_add : ℕ → ℕ → ℕ 
| nat.zero m := m
| (nat.succ n') m := nat.succ (my_add n' m)
-/

/-
∀ n, Sum numbers from 0 to n = n * (succ n) / 2.

Proof by induction. We will apply the principle of
induction for the natural numbers to two smaller
proofs: one for n = 0, and one that shows that if
the formula is true for some n' > 0, then it must
also be true succ n'.

Base case: prove (P 0): show sum from 0 to 0 = (0 * 1)/2 = 0.
Inductive case: Show  P n' → P (n' + 1)
Assume P n'. The sum from 0 to n' = n' * (n' + 1) / 2.
Show (P (n' + 1)): The sum from 0 to n'+1 = (n'+1)((n'+1)+1)/2.
Do some algebra!

--- intuition
1+2+3+4+5 if we assume this is 5*6/2
(1+2+3+4+5)+6 show this is 6*7/2
sum 0 to 5 + 6! = 5*6/2 + 6

The sum from 0 to (n' + 1) = sum from 0 to n' + (n' + 1)
                           = (n'*(n'+1)/2) + (n' + 1)
                           ...
                           = (n'+1)((n'+1)+1)/2.

-/