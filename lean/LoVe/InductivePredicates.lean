import LoVe.LoVelib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace Inductive

/-
# 6. Inductive Predicates

Also called **inductively defined propositions**
They are functions of type : ... → Prop

Example:
-/
inductive Even : ℕ → Prop where
  | zero    : Even 0
  | add_two : ∀k : ℕ, Even k → Even (k+2)

theorem even_4 :
    Even 4 :=
  have even_0 : Even 0 :=
    Even.zero
  have even_2 : Even 2 :=
    Even.add_two 0 even_0
  have even_4 : Even 4 :=
    Even.add_two 2 even_2
  even_4

/-
We can think of inductive predicates as:
-/
opaque Even₂ : ℕ → Prop
axiom Even₂.zero   : Even 0
axiom Even₂.add_to : ∀k : ℕ, Even k → Even (k+2)
/-
The problem with this syntax is that it does not specify,
which numbers are not even.
The inductive definition gurantees us that we obtain
the **smallest** set possible by our introduction rules.

We can model a so-called **transition system**
-/
inductive Score : Type where
  | vs       : ℕ → ℕ → Score
  | advServ  : Score
  | advRecv  : Score
  | gameServ : Score
  | gameRecv : Score


infixr:50 " – " => Score.vs

inductive Step : Score → Score → Prop where
  | serv_0_15     : ∀n, Step (0–n) (15–n)
  | serv_15_30    : ∀n, Step (15–n) (30–n)
  | serv_30_40    : ∀n, Step (30–n) (40–n)
  | serv_40_game  : ∀n, n < 40 → Step (40–n) Score.gameServ
  | serv_40_adv   : Step (40–40) Score.advServ
  | serv_adv_40   : Step Score.advServ (40–40)
  | serv_adv_game : Step Score.advServ Score.gameServ
  | recv_0_15     : ∀n, Step (n–0) (n–15)
  | recv_15_30    : ∀n, Step (n–15) (n–30)
  | recv_30_40    : ∀n, Step (n–30) (n–40)
  | recv_40_game  : ∀n, n < 40 → Step (n–40) Score.gameRecv
  | recv_40_adv   : Step (40–40) Score.advRecv
  | recv_adv_40   : Step Score.advRecv (40–40)
  | recv_adv_game : Step Score.advRecv Score.gameRecv

infixr:45 " ↝ " => Step

theorem no_Step_to_0_0 (s : Score) :
    ¬ s ↝ 0–0 :=
  by
    intro hs
    cases hs

/-
Another example is the **Kleene Closure**
-/
inductive Star {α : Type} (R : α → α → Prop) : α → α → Prop where
  | base (a b : α) : R a b → Star R a b
  | refl (a : α) : Star R a a
  | trans (a b c : α) : (Star _ a b) → (Star _ b c) → Star _ a c

/-
We could have also written:
  | base : ∀ a b : ℕ, R a b → Star R a b
or:
  | base (a b : α) (h : R a b) : Star R a b

To summarize, every induction rule of an ind. pred. P must consist of:
* a name
* variables that may appear in the rule
* zero or more conditions that must be fulfilled (may call P recursively)
* an application of P to some arguments as the goal
-/

/-
## 6.2 Logical Symbols
-/
inductive And (a b : Prop) : Prop where
  | intro : a → b → And a b

inductive Or (a b : Prop) : Prop where
  | inl : a → Or a b
  | inr : b → Or a b

inductive Iff (a b : Prop) : Prop where
  | intro : (a → b) → (b → a) → Iff a b

inductive Exists {α : Prop} (P : α → Prop) : Prop where
  | intro (a : α) : P a → Exists P

inductive True : Prop where
  | intro : True

inductive False : Prop where

inductive Eq {α : Type} : α → α → Prop where
  | refl : ∀a : α, Eq a a

/-
There is no constructor for False because there is no proof of False
In inductive predicates we only state the rules we want to be true

The elemination rules must be derived manually
-/

/-
## 6.3 Rule Induction

We can perform induction on a proof of an inductive predicate
For example, for:
  h : Even n ⊢ P n

It is called rule induction because the induction is on
the predicate's introduction rules

Recall, that an inductive definition introduces a symbol as the least
predicate satisfying the introduction rules.
Therefore, if we can show that P 0 and ∀k, P k → P (k + 2) hold,
then P is either Even itself or greater than Even.
As a result, Even n implies P n.
-/
theorem mod_2_if_Even (n : ℕ) (hE : Even n) :
    n % 2 = 0 :=
  by
    induction hE with
    | zero            => rfl
    | add_two k hk ih => simp[ih]


/-
## 6.4 Linear Arithmetic

The **linarith** tactic can be used to prove goals involving
linear arithmetic (in)equalities (≤, >, =, ≠)
If multipliction or division appears one argument must be a numeric constant
-/

/-
## 6.5 Elimination


-/
end Inductive
