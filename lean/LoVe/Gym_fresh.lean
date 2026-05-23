import LoVe.LoVelib

/-
1. Define a type for the natural numbers
2. Define a type for arithmetic expressions
3. Create the arithmetic expression (2+1)*x (two versions, one with . notation)
4. Create functions for arithmetic operations on natural numbers
5. Define three different power functions (default, fixed parameter, helper function)
-/

namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat

inductive AExp : Type where
  | num : Nat → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp

def y := AExp.mul (AExp.add (AExp.num (Nat.succ (Nat.succ Nat.zero))) (AExp.num (Nat.succ Nat.zero))) (AExp.var "x")
def z := ((AExp.num Nat.zero.succ.succ).add (AExp.num Nat.zero.succ)).mul (AExp.var "x")
#reduce y
#reduce z

def add : Nat → Nat → Nat
  | m, .zero    => m
  | m, .succ n  => .succ (add m n)
#eval add Nat.zero.succ.succ Nat.zero.succ

def sub : Nat → Nat → Nat
  | m, .zero          => m
  | .zero, _          => .zero
  | .succ m, .succ n  => sub m n
#eval sub Nat.zero.succ Nat.zero.succ.succ

def mul : Nat → Nat → Nat
  | _, .zero    => .zero
  | m, .succ n  => add m (mul m n)
#eval mul Nat.zero.succ.succ Nat.zero.succ.succ

-- power_1 (default)
def power : Nat → Nat → Nat
  | _, .zero    => Nat.zero.succ
  | m, .succ n  => mul m (power m n)
#eval power Nat.zero.succ.succ Nat.zero.succ.succ

-- power_2 (fixed parameters)
def power2 (m : Nat) : Nat → Nat
  | .zero     => Nat.zero.succ
  | .succ n   => mul m (power2 m n)
#eval power2 Nat.zero.succ.succ Nat.zero.succ.succ

-- power_3 (helper)

def iter (α : Type) (z : α) (f : α → α) : Nat → α
  | .zero     => z
  | .succ n   => f (iter α z f n)

def power3 (m n : Nat) : Nat :=
  iter Nat Nat.zero.succ (mul m) n

#eval power3 Nat.zero.succ.succ Nat.zero.succ.succ

end MyNat
------------------------------------------------------------------------------------------------------

-- Define an add function for the built in natural numbers

def add2 : ℕ → ℕ → ℕ
  | m, 0        => m
  | m, .succ n  => Nat.succ (add2 m n)

#eval add2 3 5
#reduce add2 1 9

/-
1. Define an AExp type and eval function for add, sub, mul, div (environment function!!)
2. Define a type for lists
3. Create a list of natural numbers [0, 1, 2]
-/

inductive AExp : Type where
  | num : ℤ → AExp
  | var : String → AExp
  | add : AExp → AExp → AExp
  | sub : AExp → AExp → AExp
  | mul : AExp → AExp → AExp
  | div : AExp → AExp → AExp


def eval (env : String → ℤ) : AExp → ℤ
  | .num x    => x
  | .var x    => env x
  | .add x y   => (eval env x) + (eval env y)
  | .sub x y   => (eval env x) - (eval env y)
  | .mul x y   => (eval env x) * (eval env y)
  | .div x y   => (eval env x) / (eval env y)

#eval eval (fun _ ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

-- List type definition
/-
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List2 α → List2 α
-/

-- 1. append (explicit type)

def append (α : Type) : List α → List α → List α
  | .nil, ys       => ys
  | (x :: xs), ys  => .cons x (append α xs ys)

#eval append ℕ [1] [2]
#eval append _ [1, 2] [9]


-- 2. append (implicit type)

def append2 {α : Type} : List α → List α → List α
  | .nil, ys      => ys
  | (x::xs), ys   => .cons x (append2 xs ys)

#eval append2 [1] [2]
#eval @append2 ℕ [3, 4, 5] [1]


-- 3. reverse (++ for append)

def reverse {α : Type} : List α → List α
  | .nil      => .nil
  | x :: xs   => (reverse xs) ++ (x :: List.nil)

#eval reverse [1, 2, 3]


/-
Give definitions for true statements (theorems) for
1. addition is comm
2. distributiv
3. double reversed List = List
-/
namespace SorryTheorems

theorem add_comm (m n : ℕ) :
    m + n = n + m :=
  sorry

theorem dis (x y z : ℤ) :
    (x + y) * z = x * z + y * z :=
  sorry

theorem rev {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

end SorryTheorems


theorem fst_of_two_props :
    ∀ (a b : Prop), a → b → a :=
  by
    sorry

theorem prop_comp :
  ∀ a b c : Prop, (a → b) → (b → c) → a → c :=
by
  sorry

theorem prop_comp_para (a b c : Prop) (hab : a → b) (hbc : b → c) (ha : a) :
    c :=
  by
    sorry

theorem and_swap (a b : Prop) :
     a ∧ b → b ∧ a :=
  by
    sorry

theorem Eq_trans_symm {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    sorry

theorem Eq_trans_symm_rw {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
by
  sorry

theorem Eq_trans_symm_rw_twist {α : Type} (a b c : α) (hab : b = a) (hcb : c = b) :
  a = c :=
by
  sorry


namespace MyNats
/-
inductive Nat : Type where
  | zero : Nat
  | succ : Nat → Nat
-/

def add : ℕ → ℕ → ℕ
  | m, .zero    => m
  | m, .succ n  => .succ (add m n)

def mul : Nat → Nat → Nat
  | _, .zero    => .zero
  | m, .succ n  => add m (mul m n)

theorem add_zero2 (n : ℕ) :
    add 0 n = n :=
  by
    sorry

theorem add_succ2 (m n : ℕ) :
    add (.succ m) n = .succ (add m n) :=
  by
    sorry

/-
Goal 1: add m.succ (n' + 1) = (add m (n' + 1)).succ
add : m, .succ n  => .succ (add m n)
=> (add m.succ n').succ

Goal 2: (add m.succ n').succ = (add m (n' + 1)).succ
ih : add m.succ n' = (add m n').succ
=> (add m n').succ.succ

Goal 3: (add m n').succ.succ = (add m (n' + 1)).succ
add : m, .succ n  => .succ (add m n)
=> (add m n').succ.succ = (add m n').succ.succ
-/

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    sorry

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    sorry

-- Tells ac_rfl that add is assoc and comm
instance Associative_add : Std.Associative add :=
  {assoc := add_assoc}

instance Commutative_add : Std.Commutative add :=
  {comm := add_comm}

theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    sorry

end MyNats

namespace Forward

theorem fst_of_two_probs :
    ∀ a b : Prop, a → b → a :=
  sorry

theorem prop_comp :
    ∀ a b c : Prop, (a → b) → (b → c) → a → c :=
  sorry

--use another theorem with arguments
theorem add_comm_0_l (n : ℕ) :
    0 + n = n + 0 :=
  sorry

theorem Add_swap_structured :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  sorry

theorem Add_swap_tactical :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  sorry

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  sorry

def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  sorry

theorem Nat_exists_double_iden_no_show :
    ∃n : ℕ, double n = n :=
  sorry

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  sorry

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  sorry

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  sorry

theorem beast_666 (beast : ℕ) :
    (∀ n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  sorry

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  sorry

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  sorry

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  sorry

def reverse {α : Type} : List α → List α
  | .nil    => .nil
  | x :: xs => reverse xs ++ [x]

theorem reverse_append_tac {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ (reverse xs) :=
  sorry

theorem reverse_reverse_tac {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  sorry

/-
theorem reverse_append_pm {α : Type} :
  sorry

theorem reverse_reverse_pm {α : Type} :
  sorry
-/

end Forward

namespace Functional

/-
Give the base and induction case for each goal

1. n : ℕ ⊢ P[n]

->
->
-----------------------------------
2. hQ : Q, n : ℕ, hR : R[n] ⊢ S[n]

->
->
-----------------------------------
3. xs : List α ⊢ P[xs]

->
->
-/

-- Nat.succ.inj
theorem succ_neq_self (n : ℕ) :
    Nat.succ n ≠ n :=
  by
    sorry

-- Define a function that counts the number of elements in a list for which p holds.
-- Use pattern matching at the top and second level (match-with)

-- Define a min-function using if-then-else


-- Define a structure for RGB


-- Define an extension with alpha values


-- Define two pure green colors and extend one with an alpha value




-- Define a shuffle function which rotates all values of a RGB to the left


-- Proof that shuffeling three times neutralizes itself


-- Define a type class Inhabited which allows a default value for a type


-- Create an instance of Inhabited for ℕ


-- Create an instance of Inhabited for Lists


-- Create '' for Tupels (types of both elements must be instances)


-- Define a function that returns the head of a list or the default value for an empty list


-- Prove the theorem that the head of the nested head of a list is the same as the head

-- Define the two semantic type classes for associativity and commutativity for binary operators


-- Make add on ℕ instance of those two type classes



-- Repeat the head_head theorem, this time with a case distinction
/-
theorem head_head_case {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  sorry


-- alternative for structured proofs
theorem head_head_structured {α : Type} [Inhabited α] (xs : List α) :
    head [head xs] = head xs :=
  match xs with
  | []          => by rfl
  | (x :: xs)   => by rfl
-/

-- use a new-learned tactic which abuses the injectivity of constructors
theorem injection_example {α : Type} (x y : α) (xs ys : List α) (h :  x :: xs = y :: ys) :
    x = y ∧ xs = ys :=
  sorry

theorem distinctness_example {α : Type} (y : α) (ys : List α) (h : [] = y :: ys) :
    False :=
  sorry

-- define a map function for lists

/-
theorem map_ident {α : Type} (xs : List α) :
    map (fun x ↦ x) xs = xs :=
  sorry

theorem map_succ {α β γ : Type} (f : α → β) (g : β → γ) (xs : List α) :
    map g (map f xs) = map (fun x ↦ g (f x)) xs :=
  sorry

theorem map_append {α β : Type} (f : α → β) (xs ys : List α) :
    map f (xs ++ ys) = map f xs ++ (map f ys) :=
  sorry
-/

-- define a tail function for lists


-- define a function head that ensures the call does not happen on []


-- define a zip function


-- define a length function



/-
theorem min_add_add (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  by
    cases Classical.em (m ≤ n) with
    | inl h => simp [min, h]
    | inr h => simp [min, h]

theorem min_add_add_match (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  match Classical.em (m ≤ n) with
  | Or.inl h => by simp [min, h]
  | Or.inr h => by simp [min, h]

theorem min_add_add_if (l m n : ℕ) :
    min (m + l) (n + l) = min m n + l :=
  if h : m ≤ n then
    by simp [min, h]
  else
    by simp [min, h]

theorem length_zip {α β : Type} (xs : List α) (ys : List β) :
    length (zip xs ys) = min (length xs) (length ys) :=
  by
    induction xs generalizing ys with
    | nil           => simp [zip, min, length]
    | cons x xs' ih =>
      cases ys with
      | nil        => rfl
      | cons y ys' => simp [zip, length, ih ys', min_add_add]

theorem map_zip {α α' β β' : Type} (f : α → α')
      (g : β → β') :
    ∀xs ys,
      map (fun ab : α × β ↦
          (f (Prod.fst ab), g (Prod.snd ab)))
        (zip xs ys) =
      zip (map f xs) (map g ys)
  | x :: xs, y :: ys => by simp [zip, map, map_zip f g xs ys]
  | [],      _       => by rfl
  | _ :: _,  []      => by rfl
-/

-- define a binary tree object


-- define a mirror function for trees

/-
theorem mirror_mirror {α : Type} (t : Tree α) :
    mirror (mirror t) = t :=
  sorry

theorem mirror_Eq_nil_Iff {α : Type} :
    ∀ t : Tree α, mirror t = Tree.nil ↔ t = Tree.nil
  sorry
-/

end Functional
