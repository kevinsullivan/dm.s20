

/- *** OBJECTS *** -/


/-
We aim to use predicate logic to express ideas about things 
that we care about. We need a way to represent such things. 
To this end, predicate logics allow us to define and use
syntactic "terms" (strings of symbols) that we take to
represent things that we care about. Here we see that the
providers of Lean have already defined certain sets of 
terms that we can use to represent natural numbers,
Boolean truth values, strings, pairs and lists of other
objects, and much more. 

A key idea that we will see in much greater depth soon
enough is that having defined sets of terms, we can then
define functions that operate on such terms. You will
see various operations (functions) involving natural
numbers, Boolean truth values, strings, pairs, and other
kinds of terms in this lesson. 
-/


/- ** Natural numbers ** -/

#eval nat.zero
#eval 0
-- 0 is nice notation for nat.zero

-- 1 is notation for (nat.succ nat.zero)
#eval nat.succ nat.zero
#eval 1

-- all the rest follow, e.g.,
-- 2 is notation of (nat.succ 1)
#eval nat.succ (nat.succ nat.zero)
#eval nat.succ 1
#eval 2


-- functions

-- predecessor, unary
#eval nat.pred 3
#eval nat.pred 1
#eval nat.pred 0    -- hmm

-- addition
#eval nat.add 2 3
#eval 2 + 3         -- infix notation

-- multiplication
#eval nat.mul 2 3
#eval 2 * 3         -- notation for mul

-- subtraction
#eval nat.sub 4 1
#eval 4 - 1         -- infix notation

#eval 5 / 2         -- notation for div
#eval nat.div 5 1       --
#eval 5 % 2         -- notation for mod

-- exponentiation
#eval 2^4 

-- what terms represent 4?

/- ** Booleans ** -/

-- true
#eval bool.tt   -- typename.fieldname
#eval tt        -- bool namespace open 
#eval succ 1    -- namespace closed

-- false
#eval ff

-- functions

-- not
#eval bnot tt

-- and
#eval band bool.tt bool.ff

-- or 
#eval band bool.tt bool.ff



/- ** Strings  ** -/

#eval "Hello, "
#eval "Logic!"
#eval string.length "Hello, "
#eval string.append "Hello, " "Logic!"

