import .propositional_logic_syntax_and_semantics



def mth_bit_from_right_in_binary_representation_of_n: ℕ → ℕ → ℕ  
| 0 n := n % 2              -- return rightmost bit
| (nat.succ m') n :=        -- shift right n and recurse on m
    mth_bit_from_right_in_binary_representation_of_n m' (n/2) 



def bit_as_nat_to_bool : ℕ → bool
| 0 := ff
| _ := tt



def mth_interpretation_for_n_vars (m n: ℕ) : var → bool :=
if (m >= 2^n)
    then λ v, ff
else
    λ v : var, 
    match v with
    | (var.mk i) := 
        if i >= n then ff 
        else bit_as_nat_to_bool 
                (mth_bit_from_right_in_binary_representation_of_n i m)
    end



def interps_helper : nat → nat → list (var → bool)
| 0 n := list.cons (mth_interpretation_for_n_vars 0 n) list.nil
| (nat.succ m') n := 
    list.cons 
        (mth_interpretation_for_n_vars (nat.succ m') n)
        (interps_helper m' n)



def enumeration_of_interpretations_for_n_vars : ℕ → list (var → bool)
| nat.zero := []
| n := interps_helper (2^n-1) n



def map_pEval_over_interpretations_for_prop_with_n_vars (p : pExp) (n : ℕ) : list bool :=
list.map 
    (λ (i : var → bool), pEval p i)
    (enumeration_of_interpretations_for_n_vars n)



def isModel (i: var → bool) (e : pExp) :=
    pEval e i = tt



def valid (e : pExp) :=
    let i := enumeration_of_interpretations_for_n_vars ∀ (i : var → bool), 
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