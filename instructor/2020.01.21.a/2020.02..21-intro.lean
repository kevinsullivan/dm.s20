-- Boolean values

/-
Boolean values
-/

#eval tt
#eval ff

#eval bool.tt
#eval bool.ff


/-
Natural numbers
-/

#eval nat.zero 
#eval 0

#eval (nat.succ nat.zero)
#eval 1

#eval nat.succ (nat.succ nat.zero)
#eval 2 


/-
Strings
-/

#eval "Hello, "
#eval "Logic!"

-- Pairs

#eval prod.mk 2 3 
#eval prod.mk 2 tt
#eval prod.mk tt ff
#eval prod.mk (prod.mk 2 tt) (prod.mk "Hello" 3)
