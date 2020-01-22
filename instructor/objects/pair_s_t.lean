/-
Pair (Polymorphic)
-/

#eval prod.mk 2 3 
#eval (2, 3)        -- notation

#eval prod.mk 2 tt  -- polymorphic

#eval prod.mk       -- coding style
        tt 
        ff

#eval 
    prod.mk         -- readable style
        (prod.mk 2 tt) 
        (prod.mk "Hello" 3)
