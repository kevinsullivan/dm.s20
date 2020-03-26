inductive var : Type
| mk : ℕ → var

inductive pExp : Type
| pTrue : pExp
| pFalse : pExp
| pVar : var → pExp
| pNot : pExp → pExp
| pAnd : pExp → pExp → pExp
| pOr : pExp → pExp → pExp
| pImp : pExp → pExp → pExp
| pIff : pExp → pExp → pExp
| pXor : pExp → pExp → pExp 

/-
¬ P -- if P is true then false, otherwise (if P is false) true
P ∧ Q -- both of the proposition, P, Q, true; commutative
P ∨ Q -- at least one of P, Q is true (not xor); commutative
xor P Q -- exactly one of P, Q is true; commutative
P → Q -- 

P → Q is true if assuming that P is true means that Q must be

If it's raining, the streets are wet.
If the streets are wet, it must be raining. F
antecedent/premise      conclusion

If 0 = 1 then 10 = 10.

False -> False
False -> True
True -> True
True -> False

From false anything follows
Given any proposition, P, False → P is true.

tt tt tt
tt ff ff
ff tt tt
ff ff tt

-/

def bimp : bool → bool → bool
| tt tt := tt
| tt ff := ff
| ff tt := tt
| ff ff := tt

open pExp

def pEval : pExp → (var → bool) → bool
| pTrue _ := tt 
| pFalse _ := ff
| (pVar v) i := i v
| (pNot e) i := bnot (pEval e i)
| (pAnd e1 e2) i := band (pEval e1 i) (pEval e2 i) 
| (pOr e1 e2) i := bor (pEval e1 i) (pEval e2 i)
| (pImp e1 e2) i := bimp (pEval e1 i) (pEval e2 i)
| (pIff e1 e2) i := tt  --stubbed out
| (pXor e1 e2) i := xor (pEval e1 i) (pEval e2 i)

notation e1 ∧ e2 :=  pAnd e1 e2
notation e1 ∨ e2 :=  pOr e1 e2
notation ¬ e := pNot e
notation e1 > e2 := pImp e1 e2
notation e1 ↔ e2 := pIff e1 e2
notation e1 ⊕ e2 := pXor e1 e2

