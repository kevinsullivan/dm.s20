import .dm_nat

open hidden

def zro := dm_nat.zero
def one := dm_nat.succ zro
def two := dm_nat.succ one
def three := dm_nat.succ (dm_nat.succ (dm_nat.succ dm_nat.zero))
def four := dm_nat.succ three
def five := dm_nat.succ four
-- etc

#reduce one
#reduce two
#reduce three
#reduce four

#reduce successor four
#reduce predecessor two
