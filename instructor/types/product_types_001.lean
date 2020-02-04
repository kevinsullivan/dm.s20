namespace hidden

inductive prod_nat_nat : Type
| mk : ℕ → ℕ → prod_nat_nat

-- polymorphic
inductive prod_S_T (S T : Type) : Type
| mk : S → T → prod_S_T


def p1 := prod_nat_nat.mk 5 0
def p2 := prod_nat_nat.mk 3 2

-- polymorphic
def p3 := prod_S_T.mk 3 0
def p4 := prod_S_T.mk tt ff
def p5 := prod_S_T.mk "Hello Logic!" 3

#reduce p1

def fst : prod_nat_nat → ℕ :=
λ (p : prod_nat_nat),
    match p with
    | (prod_nat_nat.mk x _) := x
    end

-- polymorphic
def p_fst (S T : Type) : (prod_S_T S T) → S :=
λ (p : prod_S_T S T),
    match p with
    | (prod_S_T.mk x _) := x
    end

def snd : prod_nat_nat → ℕ :=
λ (p : prod_nat_nat),
    match p with
    | (prod_nat_nat.mk _ y) := y
    end

-- polymorphic 
def p_snd (S T : Type): prod_S_T S T  → T :=
λ (p : prod_S_T S T),
    match p with
    | (prod_S_T.mk _ y) := y
    end

#eval p_snd string nat p5

def set_fst : prod_nat_nat → ℕ → prod_nat_nat :=
λ (p : prod_nat_nat) (v : ℕ), 
match p with
| (prod_nat_nat.mk _ y) := prod_nat_nat.mk v y
end

def set_snd : prod_nat_nat → ℕ → prod_nat_nat :=
λ (p : prod_nat_nat) (v : ℕ), 
match p with
| (prod_nat_nat.mk x _) := prod_nat_nat.mk x v
end

def swap : prod_nat_nat → prod_nat_nat :=
λ (p : prod_nat_nat), 
match p with
| (prod_nat_nat.mk x y) := prod_nat_nat.mk _ _
end

#eval fst p1
#eval fst p2
#eval snd p1
#eval snd p2
#reduce set_fst p1 7
#reduce set_snd p1 7

end hidden