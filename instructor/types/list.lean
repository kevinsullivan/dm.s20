/-
A list abstract data type.
-/

namespace hidden

/-
A list is either empty (nil) or it is
"cons"tructed from an element, h, at
its "head" (h) and from a smaller list,
t, as its "tail".
-/

inductive list (α : Type) : Type
| nil {} : list
| cons (h : α) (t : list) : list

/-
Notes: α in final type is implicit, and 
from this Lean also infers α as the type
argument for the type of t.
-/

end hidden