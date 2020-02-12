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


def zro := dm_nat.zero
def one := dm_nat.succ zro
def two := dm_nat.succ one
def three := dm_nat.succ (dm_nat.succ (dm_nat.succ dm_nat.zero))
def four := dm_nat.succ three
def five := dm_nat.succ four


def successor (n : dm_nat) :=
    dm_nat.succ n


def predecessor (n : dm_nat) :=
match n with
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ n') := n'
end



end hidden