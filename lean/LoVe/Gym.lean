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
    intro a b ha hb
    clear hb
    exact ha

theorem prop_comp :
  ∀ a b c : Prop, (a → b) → (b → c) → a → c :=
by
  intro a b c hab hbc ha
  apply hbc
  apply hab
  exact ha

theorem prop_comp_para (a b c : Prop) (hab : a → b) (hbc : b → c) (ha : a) :
    c :=
  by
    apply hbc
    apply hab
    exact ha

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
    apply Eq.trans
    · exact hab
    · exact (Eq.symm hcb)

theorem Eq_trans_symm_rw {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
by
  rw[hab, hcb]

theorem Eq_trans_symm_rw_twist {α : Type} (a b c : α) (hab : b = a) (hcb : c = b) :
  a = c :=
by
  rw[← hab, hcb]


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
    | zero        => rfl
    | succ n' ih  => rw[add, ih]

theorem add_succ2 (m n : ℕ) :
    add (.succ m) n = .succ (add m n) :=
  by
    induction n with
    | zero        => rw[add, add]
    | succ n' ih  => rw[add, add, ih]
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
    | succ n' ih  => rw[add, add_succ2, ih]

theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero        => rw[add, add]
    | succ n' ih  => rw[add, add, ih]
                     rfl

-- Tells ac_rfl that add is assoc and comm
instance Associative_add : Std.Associative add :=
  {assoc := add_assoc}

instance Commutative_add : Std.Commutative add :=
  {comm := add_comm}


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
  assume hab : a → b
  assume hbc : b → c
  assume ha : a
  show c from
    hbc (hab ha)

--use another theorem with arguments
theorem add_comm_0_l (n : ℕ) :
    0 + n = n + 0 :=
  add_comm 0 n

theorem Add_swap_structured :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  fix a b : Prop
  assume hab : a ∧ b
  show b ∧ a from
    have hb : b :=
      And.right hab
    have ha : a :=
      And.left hab
    And.intro hb ha

theorem Add_swap_tactical :
    ∀ a b : Prop, a ∧ b → b ∧ a :=
  by
    intro a b hab
    apply And.intro
    · exact And.right hab
    · exact And.left hab

-- Or.elim : a ∨ b → (a → c) → (b → c) → c
theorem Or_swap (a b : Prop) :
    a ∨ b → b ∨ a :=
  assume hab : a ∨ b
  show b ∨ a from
    Or.elim hab
      (assume ha : a
      Or.inr ha)
      (assume hb : b
      Or.inl hb)


def double (n : ℕ) : ℕ :=
  n + n

theorem Nat_exists_double_iden :
    ∃n : ℕ, double n = n :=
  Exists.intro 0
    (by
      rw[double])

theorem modus_ponens (a b : Prop) :
    (a → b) → a → b :=
  assume hab : a → b
  assume ha : a
  hab ha

theorem not_not_intro (a : Prop) :
    a → ¬¬ a :=
  assume ha : a
  assume h!a : (a → False)
  h!a ha

theorem Forall.one_point {α : Type} (t : α) (P : α → Prop) :
    (∀ x, x = t → P x) ↔ P t :=
  Iff.intro
    (assume hL : ∀ x, x = t → P x
     show P t from
      by
        apply hL t
        rfl)
    (assume hR : P t
     show ∀ x, x = t → P x
      by
        intro x hxt
        rw[hxt]
        exact hR)

theorem beast_666 (beast : ℕ) :
    (∀ n, n = 666 → beast ≥ n) ↔ beast ≥ 666 :=
  Forall.one_point 666 (fun n ↦ beast ≥ n)

theorem Exists.one_point {α : Type} (t : α) (P : α → Prop) :
    (∃x : α, x = t ∧ P x) ↔ P t :=
  Iff.intro
    (assume hL : ∃ x, x = t ∧ P x
     show P t from
      Exists.elim hL
        (by
          intro a hLL
          rw[← And.left hLL]
          exact And.right hLL))
    (assume hR : P t
     show ∃ x, x = t ∧ P x from
      Exists.intro t
        (by
          apply And.intro
          · rfl
          · exact hR))

theorem two_mul_example_have (m n : ℕ) :
    2 * m + n = m + n + m :=
  have h1 : 2 * m + n = m + m + n :=
    by
      rw[Nat.two_mul]
  have h2 : m + m + n = m + n + m :=
    by
      ac_rfl
  Eq.trans h1 h2


theorem two_mul_example (m n : ℕ) :
    2 * m + n = m + n + m :=
  calc
    2 * m + n = m + m + n :=
      by
        rw[Nat.two_mul]
    _ = m + n + m :=
      by
        ac_rfl

end Forward
