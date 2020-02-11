import .dm_nat

open hidden

def zero := dm_nat.zero
def one := dm_nat.succ(dm_nat.zero) -- succ
def two := successor one
def three := successor two
def four := dm_nat.succ(three)
-- etc

#reduce one
#reduce two
#reduce three
#reduce four

#reduce successor four
#reduce predecessor two
