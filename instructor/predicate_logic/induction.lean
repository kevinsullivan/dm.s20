/-
Proof strategies.

- direct proof: use established facts

- by negation: to prove ¬ P, assume P;
  show that this yields a contradiction,
  from which a proof of false can then 
  be derived. This shows P → false, and
  that is the definition of ¬ P.

  - by contradiction : to prove P, assume
    ¬ P and show that this leads to a
    contradiction, from which a proof of
    false can be derived. This proves
    ¬ P → false, which is equivalent to
    ¬ ¬ P. The apply the *classical* rule
    of negation elimination to deduce P.with

    - Today: proof by induction.
-/

/-

Prove this: ∀ (m : ℕ), 0 + m = m

Proof: By the definition of addition,
and specifically by the first of the
two cases, which tells us that for any
m, 0 + m = m. 

-/

def my_add : ℕ → ℕ → ℕ 
| nat.zero m := m
| (nat.succ n') m := nat.succ (my_add n' m)

example : ∀ (m : ℕ), my_add 0 m = m
| _ := by simp [my_add]

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

example : ∀ (n : ℕ), my_add n 0 = n
| _ := by simp [my_add]

/-
We have no rule (yet) for adding zero 
on the right, so simplifying using the
definition of my_add doesn't work.with
Instead, we need to try a whole different
proof strategy.
-/

/-
Here's the idea: 

- every inductively defined type has a
  corresponding induction rule

- It's a rule for showing that some
  proposition is true for *every* value
  of the given type

- The induction principle for ℕ is this:
  ∀ P : ℕ → Prop,
  P 0 → 
  ((∀ n' : ℕ), P n' → P (nat.succ n')) → 
  ∀ n, P n

In other words, for any predicate/property
P, to show ∀ (n : ℕ), P n, it *suffices* 
to show the following: 
    (1) P 0, 
    (2) (∀ n' : ℕ), P n' → P (nat.succ n')
-/

/-
Example: We want to prove ∀ n, n + 0 = n.
(1) Case: n = 0. By first rule of my_add.
(2) Case: n = nat.succ n': 
    Show P n' → P (nat.succ n').
    What does P n' say? my_add n' 0 = n'
    So *assume* P n', now show P (nat.succ n')
    That is, show (my_add (nat.succ n') 0 = (nat.succ n')) 

-/

