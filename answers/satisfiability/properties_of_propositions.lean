import .propositional_logic_syntax_and_semantics

def isModel (i: var → bool) (e : pExp) :=
    pEval e i = tt

def valid (e : pExp) :=
    ∀ (i : var → bool), 
        isModel i e

def satisfiable (e : pExp) :=
    ∃ (i : var → bool), 
        isModel i e

def unsatisfiable (e : pExp) :=
    ∀ (i : var → bool),
        ¬ isModel i e

def unsatisfiable' (e : pExp) :=
    ¬ ∃ (i : var → bool),
        isModel i e

def unsatisfiable'' (e : pExp) :=
    ¬ satisfiable e

def satisfiable_but_not_valid (e : pExp) :=
    (satisfiable e) ∧ ¬ (valid e)

-- def puzzle := ∃ (e : pExp), (satisfiable e) ∧ ¬ (valid e)