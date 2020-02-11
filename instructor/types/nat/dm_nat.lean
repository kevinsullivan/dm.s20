/-
Our own implementation of Lean's nat type.
We call it dm_nat to avoid any possible name
conflicts. We also leave the type's namespace
closed.
-/

namespace hidden

inductive dm_nat : Type
| zero
| succ (n' : dm_nat)


def successor (n : dm_nat) :=
    dm_nat.succ n


def predecessor (n : dm_nat) :=
match n with
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ n') := _
end



end hidden