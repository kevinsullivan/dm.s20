-- Function expressions / lambda abstraction 
-- anonymous functions

#check λ (n : ℕ), 0
#check λ (n : ℕ), n
#check λ (a b : ℕ), a+b
#check λ (a b c x: ℕ), a*x^2 + b*x + c

-- Application expressions

#check (λ (n : ℕ), 0) 5
#check (λ (n : ℕ), n) 5
#check (λ (a b : ℕ), a+b) 3 2
#check (λ (a b c x: ℕ), a*x^2 + b*x + c) 1 2 3 10

-- Giving functions names

def z := λ (n : ℕ), 0
def id_nat := λ (n : ℕ), n
def add := λ (a b : ℕ), a+b
def quad := λ (a b c x: ℕ), a*x^2 + b*x + c

-- Use names as shorthands

#eval z 5
#eval id_nat 5
#eval add 2 3
#eval quad 1 2 3 10

-- extra: partial evaluation

def q := quad 1 2 3
#check q
#eval q 10
#eval q 0
#eval q 5

-- Lambda-style
-- C-style
-- By cases
-- Tactic script


-- C-style

def z' (n : ℕ) := 0
def id_nat' (n : ℕ) := n
def add' (n m : ℕ) := n + m
def quad' (a b c x : ℕ) := a*x^2 + b*x + c

#reduce z' -- same function as z exactly

-- By cases

def z'' : ℕ → ℕ 
| _ := 0

def id_nat'' : ℕ → ℕ 
| n := n

def add'' : ℕ → ℕ → ℕ 
| n m := n + m

def quad'' : ℕ → ℕ → ℕ → ℕ → ℕ 
| a b c x := a*x^2 + b*x + c

def if_then_else : bool → ℕ → ℕ → ℕ 
| tt n m := n
| ff n m := m

#eval if_then_else ff 3 4

def ite' (b : bool) (n m : ℕ) :=
    match b with
    | tt := n
    | ff := m
    end

def ite'' : bool → ℕ → ℕ → ℕ := 
    λ (b : bool) (n m : ℕ), 
        match b with
        | tt := n
        | ff := m
        end


-- Quick preview: higher-order functions

def inc (n : ℕ) := n + 1
def sq (n : ℕ) := n^2

def is := inc ∘ sq  -- function composition
#eval is 7

-- How to implement it yourself
-- Takes two functions and returns composition
def comp (f g : ℕ → ℕ) :=
    λ (n : ℕ), 
        f (g n)

#eval (comp inc sq) 7




















-- (anonymous) function expression 

#check λ (n : ℕ), 0
#check λ (n : ℕ), n
#check λ (a b : ℕ), a + b
#check λ (a b c x : ℕ), a*x^2 + b*x +c


-- function application terms

#check (λ (a b c x : ℕ), a*x^2 + b*x +c) 1 2 3 10
#eval (λ (a b c x : ℕ), a*x^2 + b*x +c) 1 2 3 10
#eval (λ (a b : ℕ), a + b) 3 4
#eval (λ (n : ℕ), n) 5

-- binding names to function

def z := λ (n : ℕ), 0
def id_nat := λ (n : ℕ), n
def add := λ (a b : ℕ), a + b
def quad := λ (a b c x : ℕ), a*x^2 + b*x + c

-- function application expressions

#eval z 5
#eval id_nat 5
#eval add 2 3
#eval quad 1 2 3 10

-- C-style

def z' (n : ℕ) := 0
#reduce z'

-- By cases

def z'' : ℕ → ℕ 
| _ := 0

-- C style

def id_nat' (n : ℕ) := n

-- By cases

def id_nat'' : ℕ → ℕ 
| n := n

-- C style

def quad' (a b c x: ℕ) := 
    a*x^2 + b*x + c

-- By cases

def quad'' : ℕ → ℕ → ℕ → ℕ → ℕ 
| a b c x := a*x^2 + b*x + c

-- Multiple types of arguments

def if_then_else (b : bool) (n m : ℕ) :=
match b with
| tt := n
| _ := m
end

-- lambda style

def my_ite : bool → ℕ → ℕ → ℕ :=
    λ (b : bool) (n m : ℕ),
        match b with 
        | tt := n
        | ff := m
        end

def my_ite' :  bool → ℕ → ℕ → ℕ
| tt n _ := n
| _ _ m := m
