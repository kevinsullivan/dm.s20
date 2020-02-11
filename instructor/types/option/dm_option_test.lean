import .dm_option

open hidden 

/-
Because the type argument is now
implicit, if we want to give it
explicitly, we need to turn off
implicit args with @.
-/

def o1 := @dm_option.none       -- Hmm. Check it.

#check @dm_option.none 
-- Ah, partial evaluation

-- Now we give type arg explicitly
def o2 := @dm_option.none bool   

def o3 := dm_option.some tt

-- Now we see partial func p
#reduce p 0
#reduce p 1
#reduce p 2
-- etc