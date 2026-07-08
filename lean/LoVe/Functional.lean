import LoVe.LoVelib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace Functional

/-
# 5. Functional Programing

## 5.1 Inductive Types

inductive Nat : Type where
  | nil   : Nat
  | succ  : Nat -> Nat

* defines type Nat, creates constants Nat.nil and Nat.succ called **constructors**
* "no junk, no confusion"


## 5.2 Structural Induction

To prove
  n : ℕ ⊢ P[n]
by structural induction, it suffices to show the base case and the induction step (**subgoals**):
  ⊢ P[0]
  k : ℕ, ih : P[k] ⊢ P[k+1]

More general for extra hypotheses depending on n (or not):
  hQ : Q, n : ℕ, hR : R[n] ⊢ S[n]
Structural induction on n :
  hQ : Q, hR : R[0] ⊢ S[0]
  hQ : Q, k : ℕ, ih : R[k] -> S[k], hR : R[k+1] ⊢ S[k+1]

For lists with goal
  xs : List α ⊢ P[xs]
structural induction yields
  ⊢ P[[]]
  ys : List α, y : α, ih : P[ys] ⊢ P[y :: ys]

-/
theorem Nat.succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
  by
    induction n with
    | zero        => simp
    | succ n' ih  => intro hsucc; apply ih; apply Nat.succ.inj hsucc


/-
## 5.3 Structural Recursion

Allows to "peel" of one constructor of the value we recurse on
-/
def fact : ℕ -> ℕ
  | 0     => 1
  | n + 1 => (n + 1) * fact n
/-
* guranteed to terminate
* for structural recursion: as many cases as constructors

In general, defining equations (instead of opaque, axiom) can be used in computations (e.g. rfl)


## 5.4 Pattern Matching Expressions

**match-with**-expressions allow pattern matching deeply within terms
-/
def bcount {α : Type} (p : α -> Bool) : List α -> ℕ
  | []      => 0
  | x :: xs => match p x with
                | true  => 1 + bcount p xs
                | false => bcount p xs
/-
We cannot match on a proposition (of type Prop)
But we can use **if-then-else**
-/
def min (a b : ℕ) : ℕ :=
  if a ≤ b then a else b
/-
This requires a decidable(executable) proposition
Given here, because Lean can reduce a ≤ b with concrete arguments
Lean keeps track of decidability via "type classes"


## 5.5 Structures

Structures (records) are essentially non-recursive single-constructor inductive types
-/
structure RGB₁ where
  red   : ℕ
  green : ℕ
  blue  : ℕ
/-
≃
-/
inductive RGB : Type where
  | mk : ℕ -> ℕ -> ℕ -> RGB
def RGB.red : RGB -> ℕ
  | mk r _ _ => r
def RGB.green : RGB -> ℕ
  | mk _ g _ => g
def RGB.blue : RGB -> ℕ
  | mk _ _ b => b

/-
We can define a structure as the extension of an existing structure :
-/
structure RGBA extends RGB₁ where
  α : ℕ
/-
Values can be specified in a variety of syntaxes:
-/
def pureR : RGB₁ :=
  RGB₁.mk 0xff 0x00 0x00

def pureG : RGB₁ :=
  { red     := 0x00
    green   := 0xff
    blue    := 0x00
  }


def shuffle (c : RGB₁) : RGB₁ :=
  RGB₁.mk c.green c.blue c.red

theorem shuffle_shuffle (c : RGB₁) :
    shuffle (shuffle (shuffle c)) = c :=
  by
    rfl


/-
## 5.6 Type Classes

A type class is a structure type combining abstract constants and their properties.
A type can be declared an instance of a type class by providing
concrete definitions for the constants and proving that the properties hold.
-/
class Inhabited (α : Type) : Type where
  default : α
/-
Any type having at least one element can be an instance of the Inhabitated type class
-/
instance Nat.Inhabited : Inhabited ℕ :=
  { default := 0 }

instance List.Inhabited {α : Type} : Inhabited (List α) :=
  { default := [] }


def head {α : Type} [Inhabited α] : List α → α
| []      => Inhabited.default
| x :: xs => x
/-
???
-/


/-
## 5.7 Lists
-/
theorem head_head_cases {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  by
    cases xs with
    | nil        => rfl
    | cons x xs' => rfl
/-
**cases** performs a case distinction on its argument but doesn't generate an ih

The structured proof version:
-/
theorem head_head_match {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  match xs with
  | List.nil        => rfl
  | List.cons x xs  => rfl


def map {α β : Type} (f : α → β) : List α -> List β
  | []        => []
  | x :: xs   => f x :: map f xs

theorem map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  by induction xs with
  | nil            => rfl
  | cons x xs' ih  => simp[map, ih]

theorem map_comp {α β γ : Type} (f : α -> β) (g : β -> γ) (xs : List α) :
    map (fun x ↦ g (f x)) xs = map (fun x ↦ g x) (map (fun x ↦ f x) xs) :=
  by induction xs with
  | nil           => rfl
  | cons x xs' ih => simp[map, ih]

theorem map_append {α β : Type} (f : α → β) (xs ys : List α) :
    map (fun x ↦ f x) (xs ++ ys) =  (map (fun x ↦ f x) xs) ++ (map (fun x ↦ f x) ys) :=
  by
    induction xs with
    | nil           => rfl
    | cons x xs' ih => simp[map, ih]


def tail {α : Type} : List α -> List α
  | []      => []
  | _ :: xs => xs

def zip {α β : Type} : List α -> List β -> List (α × β)
  | [], ys            => []
  | xs, []            => []
  | x :: xs, y :: ys  => (x, y) :: zip xs ys

def length {α : Type} : List α -> ℕ
  | []      => 0
  | x :: xs => 1 + length xs


/-
## 5.8 Binary Trees
-/
inductive Tree (α : Type) : Type
  | nil  : Tree α
  | node : α -> Tree α -> Tree α -> Tree α

/-
Structural induction for
  t: Tree α ⊢ P[t]
by
  ⊢ P[Tree.nil]
  a : α, l r : Tree α, ih_l : P[l], ih_r : P[r] ⊢ P[Tree.node a l r]
-/

def mirror {α : Type} : Tree α -> Tree α
  | Tree.nil         => Tree.nil
  | Tree.node x l r  => Tree.node x (mirror r) (mirror l)

theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
  by
    induction t with
    | nil           => simp[mirror]
    | node x l r ih_l ih_r => simp[mirror, ih_l, ih_r]

theorem mirror_Eq_nil_Iff {α : Type} :
    ∀t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil :=
  by
    intro t
    cases t with
    | nil         => simp[mirror]
    | node x l r  => simp[mirror]


/-
## 5.9 Cases Tactic

* Performs case distinction on the specified term
* Gives rise to any as many subgoals as constructors in the definition of the term's type
* In contrast to the induction tactic, it does not produce an ih
* Can even be used for a case distinction on a Prop (one case for true, one for false)
-/

/-
## 5.10 Dependent Inductive Types

In contrast to (List α) or (Tree α), inductive types may also depend on (non-type) terms
-/
inductive Vec (α : Type) : ℕ -> Type where
  | nil                                : Vec α 0
  | cons (a : α) {n : ℕ} (v : Vec α n) : Vec α (n+1)
