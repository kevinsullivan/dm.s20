-- Namespace
namespace hidden

-- Data type bool
-- type name: dm_bool
-- type values: dm_tt, dm_ff

inductive dm_bool : Type
| dm_tt : dm_bool
| dm_ff : dm_bool

open dm_bool

def b1 := dm_ff
def b2 := dm_tt



-- Functions of type bool -> something
---- unary functions

#check 0
#check 0



def dm_not : dm_bool → dm_bool := 
    λ (b : dm_bool),
        match b with
        | dm_tt := dm_ff
        | dm_ff := dm_tt
        end

def dm_and : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
        match b1 with
        | dm_tt := b2
        | _ := dm_ff
        end

def dm_and' : dm_bool → dm_bool → dm_bool :=
    λ (b1 b2 : dm_bool),
        match b1, b2 with
        | dm_tt, dm_tt := dm_tt
        | dm_tt, dm_ff := dm_ff
        | dm_ff, dm_tt := dm_ff
        | dm_ff, dm_ff := dm_ff
        end


#reduce dm_and' dm_tt dm_tt


/-
NOT

Truth table for Boolean negation (not)

arg     res
-------------
dm_tt | dm_ff
dm_ff | dm_tt

-/


---- binary function
---- ternary functions



-- End namespace
end hidden