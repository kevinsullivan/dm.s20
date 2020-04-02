import .propositional_logic_syntax_and_semantics
import .rules_of_reasoning


/-
Return mth bit from right in binary representation of n
Consider binary representation of 6. It's 101 (with an
infinite string of zeros to the left). The 0'th bit from
the right is 1. The 1'th bit from the right is 0. The
2'th bit from the right is 1. Then all the rest are 0.
-/
def mth_bit_from_right_in_binary_representation_of_n: ℕ → ℕ → ℕ  
| 0 n := n % 2              -- return rightmost bit
| (nat.succ m') n :=        -- shift right n and recurse on m
    mth_bit_from_right_in_binary_representation_of_n m' (n/2) 


/-
Covert 0 or 1 to tt and ff respectively. Any non-negative
argument is converted to ff. Introduces "let" construct in
Lean. Important concept in mathematics in general: give a
name to a value and then use name subsequently.
-/
def mth_bool_from_right_in_binary_representation_of_n : ℕ → ℕ → bool
| m n := 
    let r := mth_bit_from_right_in_binary_representation_of_n m n in
    match r with
    | 0 := tt
    | _ := ff
    end


/-
Return m'th row of truth table with n relevant variables.
That is, return m'th of 2^n interpretations. Remember that
an interpretation is a function from variables to Booleans.

The complication is that the set of variables is infinite
and we need to return something for any value of m and n.
So, if m (the row number) is greater than 2^n-1, we just
return an all-false interpretation. 

Furthermore, given an interpretation, we need to return a
Boolean value for any variable index. For indices greater
than n-1, we just return false.

The way to understand this visually is that any truth
table extends infinitely to the right, but is all false
values beyond the n variables we care about; and it also
extends infinitely far down, but every row is all false
beyond the 2^n rows that we care about.
-/
def mth_interpretation_for_n_vars (m n: ℕ) : (var → bool) :=
if (m >= 2^n)
    then λ v, ff
else
    λ v : var, 
    match v with
    | (var.mk i) := 
        if i >= n then ff 
        else (mth_bool_from_right_in_binary_representation_of_n i m)
    end

/-
Now we define a function to generate a standard truth table (except
for the output column, i.e., just the input tows) as a list of 2^n 
interpretations.
-/

def interpretations_helper : nat → nat → list (var → bool)
| 0 n := list.cons (mth_interpretation_for_n_vars 0 n) list.nil
| (nat.succ m') n := 
    list.cons 
        (mth_interpretation_for_n_vars (nat.succ m') n)
        (interpretations_helper m' n)



def interpretations_for_n_vars : ℕ → list (var → bool)
| nat.zero := []
| n := interpretations_helper (2^n-1) n



def map_pEval_over_truth_table_for_prop (p : pExp) (n : ℕ) : list bool :=
list.map 
    (λ (i : var → bool), pEval p i)
    (interpretations_for_n_vars n)


open pExp


/-
We need to be able to represent the set of variables
in a given expression. We will represent it as a list
of variables without duplicates.
-/

/-
When adding a variable to a set, we need to be sure it
is not already in the set. Se we need to be able to check
if one variable is *equal* to another. We define two variables
to be equal (to be the same variable) if their indices are the
same.
-/
def eq_var : var → var → bool
| (var.mk n) (var.mk m) := n = m


/-
We represent a set of variables as as a list without dups.
Note that here we're just giving a nice, abstract name,
var_set, to the type, list var. We can say that var_set is
a "type alias" for the type, list var.
-/
def var_set := list var 


/-
Make a new empty var set (return an empty list of vars).
-/
def mk_var_set : var_set := list.nil

/-
return true if given var v is in given var set. Note that
we do pattern matching on the result of comparing v with 
the head of the given list (representing a set of variables)
and return a result accordingly.
-/
def in_var_set : var → var_set → bool
| v [] := ff
| v (h::t) := match (eq_var v h) with | tt := tt | ff := in_var_set v t end

/-
Return union of two var sets, l1 and l2. If l1 is empty we
just return l2. Here we assume that l2 already represents a
set, i.e., is a list with no duplicates. If l2 is not empty
we check if its head is in l2. If it's not, we "add" it, and
otherwise we don't. Here we introduce the if...then...else 
in Lean.
-/
def var_set_union : var_set → var_set → var_set 
| [] l2 := l2
| (h::t) l2 :=  if (in_var_set h l2) 
                then var_set_union t l2 
                else (h::var_set_union t l2)

/-
In the code below, we need to compute the union of three
sets in some places. We provide this utility function to
make that a bit easier.
-/
def var_3_set_union : var_set → var_set → var_set → var_set 
| s1 s2 s3 := var_set_union (var_set_union s1 s2) s3


/-
Now we define a function that, when given an expression, e,
returns the set of all (and only) the variables that appear
in e.
-/

/-
We start with a helper function that takes a set of variables
we've see so far and adds to it the set of variables in a given
expression e and returns the result. The main (non-recursive)
function then uses this (recursive) function, calling it with
an initially empty set. 
-/
def set_of_variables_in_expression_helper : pExp → list var -> list var
| pTrue l := l
| pFalse l := l
| (pVar v) l :=  var_set_union [v] l
| (pNot e) l := set_of_variables_in_expression_helper e l
| (pAnd e1 e2) l:= var_3_set_union 
                        l
                        (set_of_variables_in_expression_helper e1 list.nil) 
                        (set_of_variables_in_expression_helper e2 list.nil)
| (pOr e1 e2) l := var_3_set_union 
                        l
                        (set_of_variables_in_expression_helper e1 list.nil) 
                        (set_of_variables_in_expression_helper e2 list.nil)
| (pImp e1 e2) l := var_3_set_union 
                        l
                        (set_of_variables_in_expression_helper e1 list.nil) 
                        (set_of_variables_in_expression_helper e2 list.nil)
| (pIff e1 e2) l := var_3_set_union 
                        l
                        (set_of_variables_in_expression_helper e1 list.nil) 
                        (set_of_variables_in_expression_helper e2 list.nil)
| (pXor e1 e2) l := var_3_set_union 
                        l
                        (set_of_variables_in_expression_helper e1 list.nil) 
                        (set_of_variables_in_expression_helper e2 list.nil)

def set_of_variables_in_expression : pExp → var_set
| e := set_of_variables_in_expression_helper e list.nil

/-
The cardinality of a set is the number of elements it contains. As
we represent a set as a list without duplicates, the length of the
list is the same as the cardinality of the set.
-/
def var_set_cardinality : var_set → ℕ 
| s := s.length

/-
The number of variables in an expression is thus the cardinality of
the set of variables it contains.
-/
def number_of_variables_in_expression : pExp → ℕ
| e := var_set_cardinality (set_of_variables_in_expression e)


/-
BACK TO LOGIC
-/

/-
We say an interpretation is a "model" of an expression in
logic if it makes that expression true. 
-/
def isModel (i: var → bool) (e : pExp) : bool :=
    pEval e i


/-
Given this wording, we can now state that an expression is
valid if every one of its intepretations is a model. Here is
a function that takes an expression, evaluates it for each
interpretation in a list of interpretations, and returns the
list of the resulting Boolean values.
-/
def map_pEval_over_interps : pExp → list (var → bool) → list bool
| e [] := []
| e (i::t) := (isModel i e :: map_pEval_over_interps e t)

/-
Return true if and only if every bool in a list of bools is tt.
A special case of the foldr function.
-/
def foldr_and : list bool → bool
| [] := tt
| (h::t) := band h (foldr_and t)


def is_valid (e : pExp) : bool :=
    let n := number_of_variables_in_expression e in 
    let is := interpretations_for_n_vars n in
    let rs := map_pEval_over_interps e is in 
    foldr_and rs
        
#eval is_valid ((P >> Q ∧ Q >> P) >> P ↔ Q)


#eval is_valid true_intro 

#eval is_valid false_elim 

#eval is_valid  and_intro 

#eval is_valid  and_elim_left 

#eval is_valid  and_elim_right 

#eval is_valid  or_intro_left 

#eval is_valid  or_intro_right 

#eval is_valid  or_elim 

#eval is_valid  iff_intro 

#eval is_valid  iff_intro' 

#eval is_valid  iff_elim_left

#eval is_valid   iff_elim_right 

#eval is_valid   arrow_elim 

#eval is_valid   resolution 

#eval is_valid   unit_resolution 

#eval is_valid   syllogism 

#eval is_valid   modus_tollens 

#eval is_valid   neg_elim 

#eval is_valid   excluded_middle 

#eval is_valid   neg_intro 

#eval is_valid   affirm_consequence 

#eval is_valid   affirm_disjunct 

#eval is_valid   deny_antecedent 
