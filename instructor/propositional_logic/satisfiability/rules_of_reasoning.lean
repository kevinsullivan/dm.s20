import .propositional_logic_syntax_and_semantics
import .properties_of_propositions

open pExp


def P := pVar (var.mk 0)
def Q := pVar (var.mk 1)
def R := pVar (var.mk 2)

def true_intro : pExp := pTrue
#reduce valid true_intro

def false_elim := pFalse >> P
#reduce valid false_elim 

#eval pEval false_elim _

def true_imp := pTrue >> P

def and_intro := P >> Q >> P ∧ Q

def and_elim_left := P ∧ Q >> P

def and_elim_right := P ∧ Q >> Q

def or_intro_left := P >> P ∨ Q

def or_intro_right := Q >> P ∨ Q

def or_elim := P ∨ Q >> (P >> R) >> (Q >> R) >> R

def iff_intro := (P >> Q) >> (Q >> P) >> (P ↔ Q)

def iff_intro' := (P >> Q) ∧ (Q >> P) >> (P ↔ Q)

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
#reduce valid affirm_disjunct

def deny_antecedent := (P >> Q) >> (¬ P >> ¬ Q)
