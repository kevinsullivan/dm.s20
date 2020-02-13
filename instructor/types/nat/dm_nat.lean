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


def predecessor (n : dm_nat) :=
match n with
| dm_nat.zero := dm_nat.zero
| (dm_nat.succ n') := n'
end

end hidden


-- let's look at Lean's definition of nat

#check nat

-- it's exactly as we've written it


#eval nat.succ nat.zero
#eval nat.pred (nat.succ nat.zero)
