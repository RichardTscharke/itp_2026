import LoVe.LoVelib
namespace MyNat

-- 1. Define a type for the natural numbers
inductive N where
  | zero : N
  | succ : N -> N

-- 2. Define a type for arithmetic expressions
inductive XP where
  | num : N -> XP
  | var : String -> XP
  | sum : XP -> XP -> XP
  | sub : XP -> XP -> XP
  | mul : XP -> XP -> XP
  | div : XP -> XP -> XP


-- 3. Create the arithmetic expression (2+1)*x

def x : XP := XP.var "x"
def A : XP := XP.mul (XP.sum (XP.num (N.succ (N.succ N.zero))) (XP.num (N.succ N.zero))) x
#reduce A

-- 4. Create functions for arithmetic operations on natural numbers

def a : N := N.zero.succ.succ.succ
def b : N := N.zero.succ.succ.succ.succ.succ
def f : N -> ℕ
  | N.zero => 0
  | N.succ n => 1 + (f n)

def add : N -> N -> N
  | n, N.zero => n
  | n, N.succ m => N.succ (add n m)
#eval f (add a b)

def sub : N -> N -> N
  | N.zero, _ => N.zero
  | n, N.zero => n
  | N.succ n, N.succ m => sub n m
#eval f (sub a b)
#eval f (sub b a)

def mul : N -> N -> N
  | _, N.zero => N.zero
  | n, N.succ m => add n (mul n m)
#eval f (mul a b)
#eval f (mul b a)

-- 5. Define three different power functions (default, fixed parameter, helper function)
def power : N -> N -> N
  | _, N.zero => N.zero.succ
  | n, N.succ m => mul n (power n m)
#eval f (power a b)
#eval f (power b a)

def power2 (n : N) : N -> N
  | N.zero => N.zero.succ
  | N.succ m => mul n (power2 n m)
#eval f (power2 a b)
#eval f (power2 b a)



end MyNat
------------------------------------------------------------------------------------------------------

-- Define an add function for the built in natural numbers


-- #eval add2 3 5
-- #reduce add2 1 9


-- 1. Define an AExp type and eval function for add, sub, mul, div (environment function!!)
inductive XP where
  | num : ℕ -> XP
  | var : String -> XP
  | sum : XP -> XP -> XP
  | sub : XP -> XP -> XP
  | mul : XP -> XP -> XP
  | div : XP -> XP -> XP

def eval (env : String -> ℕ) : XP -> ℕ
  | XP.num i => i
  | XP.var x => env x
  | XP.sum x y => (eval env x) + (eval env y)
  | XP.sub x y => (eval env x) - (eval env y)
  | XP.mul x y => (eval env x) * (eval env y)
  | XP.div x y => (eval env x) / (eval env y)
#eval eval (fun _ ↦ 7) (XP.div (XP.var "y") (XP.num 0))


-- 2. Define a type for lists

inductive L (α : Type) where
  | l : L α
  | x : α -> L α -> L α


-- 3. Create a list of natural numbers [0, 1, 2]

def A : L ℕ := L.x 0 (L.x 1 (L.x 2 L.l))
#reduce A


-- 1. append (explicit type)

def append (α : Type) : List α -> List α -> List α
  | [], ys => ys
  | (x :: xs), ys => x :: append α xs ys

#eval append ℕ [1] [2]
#eval append _ [1, 2] [9]


-- 2. append (implicit type)
def append2 {α : Type} : List α -> List α -> List α
  | [], ys => ys
  | (x :: xs), ys => x :: append α xs ys

#eval append2 [1] [2]
#eval @append2 ℕ [3, 4, 5] [1]


-- 3. reverse (++ for append)

def reverse {α : Type} : List α -> List α
  | [] => []
  | x :: xs => (reverse xs) ++ [x]

#eval reverse [1, 2, 3]


namespace SorryTheorems

--Give definitions for true statements (theorems) for
-- 1. addition is comm
theorem add_comm (n m : ℕ) :
  n + m = m + n :=
sorry

-- 2. distributiv
theorem dis (n m p : ℕ) :
  n * (m + p) = n * m + n * p :=
sorry

-- 3. double reversed List = List
theorem rereverse {α : Type} (xs : List α) :
  reverse (reverse xs) = xs :=
sorry

end SorryTheorems


theorem fst_of_two_props :
    ∀ (a b : Prop), a → b → a :=
  by
    intro a b ha hb
    apply ha

theorem prop_comp :
  ∀ a b c : Prop, (a → b) → (b → c) → a → c :=
by
  intro a b c hab hbc ha
  apply hbc
  apply hab
  apply ha

theorem prop_comp_para (a b c : Prop) (hab : a → b) (hbc : b → c) (ha : a) :
    c :=
  by
    apply hbc
    apply hab
    apply ha

theorem and_swap (a b : Prop) :
     a ∧ b → b ∧ a :=
  by
    intro hab
    apply And.intro
    · exact And.right hab
    · exact And.left hab

theorem Eq_trans_symm {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
    a = c :=
  by
    apply Eq.trans hab (Eq.symm hcb)

theorem Eq_trans_symm_rw {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
by
  rw[hab, hcb]

theorem Eq_trans_symm_rw_twist {α : Type} (a b c : α) (hab : b = a) (hcb : c = b) :
  a = c :=
by
  rw[<- hab, hcb]

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
    induction n with
    | zero => rw[add]
    | succ n' ih => rw[add, ih]

theorem add_succ2 (m n : ℕ) :
    add (.succ m) n = .succ (add m n) :=
  by
    induction n with
    | zero       => simp[add]
    | succ n' ih => simp[add, ih]

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
    induction n with
    | zero        => rw[add, add_zero2]
    | succ n' ih  => simp[add, add_succ2, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero        => simp[add]
    | succ n' ih  => simp[add, ih]

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
  fix a b : Prop
  assume ha : a
  assume hb : b
  ha

theorem prop_comp :
    ∀ a b c : Prop, (a → b) → (b → c) → a → c :=
  fix a b c : Prop
  assume hab : a -> b
  assume hbc : b -> c
  assume ha : a
  hbc (hab ha)

--use another theorem with arguments
theorem add_comm_0_l (n : ℕ) :
    0 + n = n + 0 :=
  add_comm 0 n

theorem Add_swap_structured :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  fix a b : Prop
  assume hab : a ∧ b
  And.intro (And.right hab) (And.left hab)

theorem Add_swap_tactical :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    · exact And.right hab
    · exact And.left hab

theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  Or.elim hab
    (assume ha : a
     Or.inr ha)
    (assume hb : b
     Or.inl hb)

def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  Exists.intro
    0
    (show double 0 = 0 from
      rfl)

theorem Nat_exists_double_iden_no_show :
    ∃n : ℕ, double n = n :=
  Exists.intro 0 (by rfl)

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a -> b
  assume ha : a
  hab ha

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  assume ha : a
  assume h!a : a -> False
  h!a ha

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hL : ∀ (x : α), x = t → P x
     show P t from
     by
      apply hL t
      rfl)
    (assume hR : P t
     fix x : α
     assume hxt : x = t
     by
      rw[hxt]
      exact hR)

theorem beast_666 (beast : ℕ) :
    (∀ n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Iff.intro
    (assume hL : ∀ n, n = 666 → beast ≥ n
     show beast ≥ 666 from
     by
      apply hL 666
      rfl)
    (assume hR : beast ≥ 666
     fix n : ℕ
     assume hn : n = 666
     show beast >= n from
     by
      rw[hn]
      exact hR)

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hL : ∃ x : α, x = t ∧ P x
     show P t from
      Exists.elim hL
        (fix a : α
         assume hLL : a = t ∧ P a
         show P t from
          have hat : a = t :=
            And.left hLL
          have hPa : P a :=
            And.right hLL
          by
            rw[← hat]
            exact hPa
          ))
    (assume hR : P t
     show ∃x : α, x = t ∧ P x from
      Exists.intro t
        (And.intro rfl hR)
      )

theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by rw[Nat.two_mul]
    _ =  m + n + m :=
      by ac_rfl

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  have h1 : 2 * m + n = m + m + n :=
    by rw[Nat.two_mul]
  have h2 : m + m + n = m + n + m :=
    by ac_rfl
  Eq.trans h1 h2


def reverse {α : Type} : List α → List α
  | .nil    => .nil
  | x :: xs => reverse xs ++ [x]

theorem reverse_append_tac {α : Type} (xs ys : List α) :
    reverse (xs ++ ys) = reverse ys ++ (reverse xs) :=
  by
    induction xs with
    | nil           => simp[reverse]
    | cons x xs' ih => simp[reverse, ih]

theorem reverse_reverse_tac {α : Type} (xs : List α) :
    reverse (reverse xs) = xs :=
  by
    induction xs with
    | nil           => simp[reverse]
    | cons x xs' ih => simp[ih, reverse, reverse_append_tac]

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
