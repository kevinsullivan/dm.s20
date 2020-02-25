/-
Our own implementation of Lean's nat type.
We call it dm_nat to avoid any possible name
conflicts. We also leave the type's namespace
closed.
-/

namespace hidden

inductive dm_nat : Type
| zero : dm_nat
| succ (n' : dm_nat) : dm_nat

def successor (n : dm_nat) :=
    dm_nat.succ n


def pred (n : dm_nat) :=
match n with
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ n') := n'
end


/-
It's essential to understand pattern
matching, i.e., destructuring, in Lean.
The second rule not only matches any
argument value that starts with "succ"
(or more precisely dm_nat.succ), but it
also temporarily binds the identifier,
n', to the *rest* of the argument value:
to the one-smaller natural number term
that comes after the "succ". For example,
if the argument is 5, n' will be bound
to 4, and that of course is exactly 
what we want to return as the value
of the predecessor of 5.

pred (S ( S (S (S (S Z)))))
pred (S          n'       )
-/



def pred2 (n : dm_nat) :=
match n with
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ dm_nat.zero) := dm_nat.zero
| (dm_nat.succ (dm_nat.succ n')) := n'
end

#reduce pred2 dm_nat.zero
#reduce pred2 (dm_nat.succ dm_nat.zero)
#reduce pred2 (dm_nat.succ (dm_nat.succ dm_nat.zero))


/-
    **** RECURSION ****
-/

-- addition as recursively iterated successorr

def add : dm_nat → dm_nat → dm_nat 
| dm_nat.zero m := m
| (dm_nat.succ n') m := dm_nat.succ (add n' m)

-- by case analysis on *both* arguments
def equals : dm_nat → dm_nat → bool
| dm_nat.zero dm_nat.zero := tt
| dm_nat.zero _ := ff
| _ dm_nat.zero := ff
| (dm_nat.succ n') (dm_nat.succ m') := equals n' m'

#eval equals dm_nat.zero dm_nat.zero
#eval equals dm_nat.zero (dm_nat.succ dm_nat.zero)
#eval equals (dm_nat.succ dm_nat.zero) dm_nat.zero 
#eval equals (dm_nat.succ dm_nat.zero) (dm_nat.succ dm_nat.zero)  
#eval equals (dm_nat.succ dm_nat.zero) (dm_nat.succ (dm_nat.succ dm_nat.zero))
#eval equals (dm_nat.succ (dm_nat.succ dm_nat.zero)) (dm_nat.succ dm_nat.zero) 


def sub : dm_nat → dm_nat → dm_nat 
| dm_nat.zero dm_nat.zero := dm_nat.zero
| dm_nat.zero _ := dm_nat.zero
| n dm_nat.zero := n
| (dm_nat.succ n') (dm_nat.succ m') := sub n' m'


#reduce sub dm_nat.zero dm_nat.zero
#reduce sub dm_nat.zero (dm_nat.succ dm_nat.zero)
#reduce sub (dm_nat.succ dm_nat.zero) dm_nat.zero 
#reduce sub (dm_nat.succ dm_nat.zero) (dm_nat.succ dm_nat.zero)  
#reduce sub (dm_nat.succ dm_nat.zero) (dm_nat.succ (dm_nat.succ dm_nat.zero))
#reduce sub (dm_nat.succ (dm_nat.succ dm_nat.zero)) (dm_nat.succ dm_nat.zero) 


def fib : dm_nat → dm_nat
| dm_nat.zero := dm_nat.zero 
| (dm_nat.succ dm_nat.zero) := (dm_nat.succ dm_nat.zero) 
| (dm_nat.succ (dm_nat.succ n'')) := add (fib n'') (fib (dm_nat.succ n''))

/-
fib 0 = 0
fib 1 = 1
fib 2 = 1
fib 3 = 2
fib 4 = 3
fib 5 = 5
fib 6 = 8
-/

#reduce fib (dm_nat.succ (dm_nat.succ dm_nat.zero))

def fac : ℕ → ℕ 
| 0 := 1 
| (nat.succ n') := (nat.succ n') * (fac n')

#eval fac 5

-- 3 + 3
/-
Let's give the convenient name, three, to the
term that we use to represent the natural number
three. We then use this shorthand to test add.
-/
def three := dm_nat.succ (dm_nat.succ (dm_nat.succ dm_nat.zero) )
#reduce add three three


-- 2 + 2
#reduce add 
        (dm_nat.succ (dm_nat.succ dm_nat.zero))
        (dm_nat.succ (dm_nat.succ dm_nat.zero))


/-
It's also essential to understand how the application
of a recursive function to an argument is evaluated. We
repeatedly apply the function definition until there are
no more applications of the given function left in the
resulting term.
-/


/-
Here, for example, is how "add two two" gets evaluated. Study this!

add 
    (dm_nat.succ (dm_nat.succ dm_nat.zero)) 
    (dm_nat.succ (dm_nat.succ dm_nat.zero))
dm_nat.succ (add (dm_nat.succ dm_nat.zero) (dm_nat.succ (dm_nat.succ dm_nat.zero)))
dm_nat.succ (dm_nat.succ (add dm_nat.zero (dm_nat.succ (dm_nat.succ dm_nat.zero))))
dm_nat.succ (dm_nat.succ (dm_nat.succ (dm_nat.succ dm_nat.zero)))
That's (our representation of) four!

Using ordinary numerals

add 2 2
succ (add 1 2)
succ (succ (add 0 2))
succ (succ (2))
= 4
-/

/- 
Using shorthands S, Z, and 4
in expression for 3 + 4:

add (S (S (S Z))) (S (S (S (S Z))))
add (S (S (S Z))) 4
S (add (S (S Z)) 4)
S (S (add (S Z) 4))
S (S (S (add Z 4)))
S (S (S (4)))
That's 7
-/


-- multiplication is defined as recursive iteration of add

def mult : dm_nat → dm_nat → dm_nat 
| dm_nat.zero m := dm_nat.zero 
| (dm_nat.succ n') m := add m (mult n' m)

#reduce mult three three

/-
4 * 3
3 + (3 * 3)
3 + (3 + (2 * 3))
-/

/-
mult 3 2
2 + mult 2 2
2 + (2 + mult 1 2)
2 + (2 + (2 + mult 0 2))
2 + (2 + (2 + 0))
= 6
-/


-- exponentiation is recursive iteration of mult

def exp : dm_nat → dm_nat → dm_nat 
| n dm_nat.zero := dm_nat.succ dm_nat.zero 
| n (dm_nat.succ m') := mult n (exp n m') 

#reduce exp three three

/-
exp 2 3
2 * exp 2 2
2 * (2 * exp 2 1)
2 * (2 * (2 * exp 2 0))
2 * (2 * (2 * (1)))
= 8
-/

-- a funtion to compute sum from 0 to n (here n down to 0)

def sum_to : dm_nat → dm_nat 
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ n') := add (dm_nat.succ n') (sum_to n')

def fac : dm_nat → dm_nat
| dm_nat.zero := dm_nat.succ dm_nat.zero
| (dm_nat.succ n') := mult (dm_nat.succ n') (fac n')

end hidden

/-
sum_to 5
5 + sum_to 4
5 + (4 + sum_to 3)
5 + (4 + (3 + sum_to 2))
5 + (4 + (3 + 2 + sum_to 1))
5 + (4 + (3 + 2 + (1 + sum_to 0)))
5 + 4 + 3 + 2 + 1 + 0
= 15
-/

-- let's look at Lean's definition of nat

#check nat

-- it's exactly as we've written it


#eval nat.succ nat.zero
#eval nat.pred (nat.succ nat.zero)
