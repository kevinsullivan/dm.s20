import .propositional_logic_syntax_and_semantics

-- Here are some variable expressions
--
def P_var := var.mk 0
def Q_var := var.mk 1
def R_var := var.mk 2
def V_3 := var.mk 4 --etc


def P := pVar P_var        -- pVar (var.mk 0) 
def Q := pVar Q_var        -- pVar Q_var
def R := pVar R_var        -- pVar R_var

#check P

def interp_all_false : var → bool
| _ := ff

def interp_all_true : var → bool
| _ := tt


-- Here's our extended semantic evaluator
#check pAnd P Q
#check P ∧ Q            -- P and Q
#check P ∨ Q            -- P or Q
#check ¬ P              -- not P
#check P > Q            -- P > Q
#check P ↔ Q


#eval pEval P interp_all_false
#eval pEval P interp_all_true


-- Examples of larger expressions
#eval pEval (pOr (pAnd P Q) R)    -- (P ∧ Q) ∨ R

#eval pEval ((P ∧ Q) ∨ R) interp_all_false
#eval pEval ((P ∧ Q) ∨ R) interp_all_true

#eval pEval (pAnd    
                (pOr 
                    P
                    Q
                )
                (pAnd
                    P 
                    Q
                )
            )
            interp_all_true

#eval pEval ((P ∨ Q) ∧ (P ∧ Q)) interp_all_true
#eval pEval (P > Q) interp_all_false
#eval pEval (P > Q) interp_all_true

def tt_ff_interp : var → bool
| (var.mk 0) := tt  -- P_var
| (var.mk 1) := ff  -- Q_var
| _ := ff

#eval pEval (P > Q) tt_ff_interp


def lots_of_fun := pAnd (pOr P Q) (pNot P)
def lots_of_fun' := (P ∨ Q) ∧ (¬ P)

def sat : var → bool
| (var.mk 0) := ff       -- P_var
| (var.mk 1) := tt       -- Q_var
| (var.mk _) := ff       -- otherwise

#eval pEval lots_of_fun sat
#eval pEval lots_of_fun' sat

-- We have found a *satisfying solution*
-- An interpretation that makes an expression true!

-- A problem that has a solution is said to be *satisfiable*
-- A problem that has no solution is said be *unsatisfiable*
-- A problem for which every interp is a solution is said to be *valid*
-- Satisfiable but not valid


-- pAnd P (pNot P)  -- P ∧ ¬ P      -- never true
-- pOr P (pNot P)   -- P ∨ ¬ P

/-
Proof by case analysis
- P=true: true ∨ false = true
- P=false: false ∨ true = true
-/


/- VALID RULES OF REASON

-- 
(P ∧ Q) → (Q ∧ P)
¬ (P ∧ Q) → (¬ P) ∨ (¬ Q)
¬ (P ∨ Q) → (¬ P ∧ ¬ Q)

-- not valid
(P → Q) → (Q → P)
-/


#eval pEval pTrue
#eval pEval pFalse
#eval pEval (pNot pTrue)
#eval pEval (pNot pFalse)

def p1 := pTrue
def p2 := pFalse
def p25 := pNot p2
def p3 := pAnd pTrue pFalse
def p4 := pOr p3 p2

#eval pEval p3
#eval pEval p4
#eval pEval (pImp p3 p4)
