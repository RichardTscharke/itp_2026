import LoVe.LoVelib

/-
1. Define a type for the natural numbers
2. Define a type for arithmetic expressions
3. Create the arithmetic expression (2+1)*x
4. Create functions for arithmetic operations on natural numbers
5. Define three different power functions (default, fixed parameter, helper function)
-/

namespace MyNat

inductive Nat : Type where
  | zero : Nat
  | succ : Nat -> Nat

inductive AExp : Type where
  | num : Nat -> AExp
  | var : String -> AExp
  | add : AExp -> AExp -> AExp
  | sub : AExp -> AExp -> AExp
  | mul : AExp -> AExp -> AExp
  | div : AExp -> AExp -> AExp

def A : AExp := AExp.mul (AExp.add (AExp.num (Nat.succ (Nat.succ Nat.zero))) (AExp.num (Nat.succ Nat.zero))) (AExp.var "x")

#reduce A

def add : Nat -> Nat -> Nat
  | n, .zero   => n
  | n, .succ m => .succ (add n m)

-- Assumption: first argument >= second argument. Else: 0
def sub : Nat -> Nat -> Nat
  | n, .zero         => n
  | .zero, _         => .zero
  | .succ n, .succ m => sub n m

def mul : Nat -> Nat -> Nat
  | .zero, _         => .zero
  | _, .zero         => .zero
  | n, .succ m       =>  add n (mul n m)

-- Division by 0 returns 0
def div : Nat -> Nat -> Nat
  | _, .zero       => .zero
  | .zero, _       => .zero
  | n, .succ .zero => n
  | n, .succ m     => div (sub n m) m

def power : Nat -> Nat -> Nat
 | _, .zero   => .succ .zero
 | n, .succ m => mul n (power n m)

def powerParam (n : Nat) : Nat -> Nat
  | .zero   => .succ .zero
  | .succ m => mul n (powerParam n m)

def iter (α : Type) (z : α) (f : α → α) : Nat → α
  | .zero   => z
  | .succ n => f (iter α z f n)

def powerIter (n m : Nat) : Nat :=
  iter Nat (.succ .zero) (mul n) m

end MyNat
------------------------------------------------------------------------------------------------------
def add : ℕ -> ℕ → ℕ
  | n, Nat.zero => n
  | n, Nat.succ m => Nat.succ (add n m)

#eval add 1 2
#reduce add 1 2

/-
1. Define an AExp type and eval function for add, sub, mul, div (environment function!!)
2. Define a type for lists
3. Create a list of natural numbers [0, 1, 2]
-/

inductive AExp : Type where
  | num : ℤ -> AExp
  | var : String -> AExp
  | add : AExp -> AExp -> AExp
  | sub : AExp -> AExp -> AExp
  | mul : AExp -> AExp -> AExp
  | div : AExp -> AExp -> AExp

def eval (env : String -> ℤ) : AExp -> ℤ
  | AExp.num i => i
  | AExp.var x => env x
  | AExp.add e1 e2 => eval env e1 + eval env e2
  | AExp.sub e1 e2 => eval env e1 - eval env e2
  | AExp.mul e1 e2 => eval env e1 * eval env e2
  | AExp.div e1 e2 => eval env e1 / eval env e2

#eval eval (fun _ ↦ 7) (AExp.div (AExp.var "y") (AExp.num 0))

/-
inductive List (α : Type) : Type where
  | nil : List α
  | cons : α → List α -> List α
-/

-- 1. append (explicit type)
def append (α : Type) : List α → List α → List α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (append α xs ys)

#eval append ℕ (.cons 1 .nil) (.cons 2 .nil)
#eval append ℕ [1] [2]
#eval append _ [1, 2] [9]

-- 2. append (implicit type)
def appendImp {α : Type} : List α → List α → List α
  | .nil, ys => ys
  | .cons x xs, ys => .cons x (appendImp xs ys)

#eval appendImp [1] [2]
#eval @appendImp ℕ [1] [2]

-- 3. append (:: for .cons)
def appendPretty {α : Type} : List α → List α → List α
  | .nil, ys => ys
  | (x :: xs), ys => x :: (appendPretty xs ys)

-- 4. reverse (++ for append)
def reverse {α : Type} : List α → List α
  | .nil    => .nil
  | x :: xs => reverse xs ++ [x]


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
    apply Eq.trans
    · exact hab
    · exact Eq.symm hcb

theorem Eq_trans_symm_rw {α : Type} (a b c : α) (hab : a = b) (hcb : c = b) :
  a = c :=
by
  rw [hab]
  rw [hcb]

theorem Eq_trans_symm_rw_twist {α : Type} (a b c : α) (hab : b = a) (hcb : c = b) :
  a = c :=
by
  rw [← hab, hcb]


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
    | succ n' ih  => simp[add, ih]

theorem add_succ2 (m n : ℕ) :
    add (.succ m) n = .succ (add m n) :=
  by
    induction n with
    | zero        => simp[add]
    | succ n' ih  => simp[add, ih]

/-
Goal 1: add m.succ (n' + 1) = (add m (n' + 1)).succ
add : m, .succ n  => .succ (add m n)
=> (add m.succ n').succ

Goal 2: (add m.succ n').succ = (add m (n' + 1)).succ
ih : add m.succ n' = (add m n').succ
=> (add m n').succ.succ = (add m (n' + 1)).succ
! simp does the rest here !
-/

theorem add_comm (m n : ℕ) :
    add m n = add n m :=
  by
    induction n with
    | zero        => simp[add, add_zero2]
    | succ n' ih  => simp[add_succ2, add, ih]


theorem add_assoc (l m n : ℕ) :
    add (add l m) n = add l (add m n) :=
  by
    induction n with
    | zero        => simp[add]
    | succ n' ih  => simp[add, ih]


instance Associative_add : Std.Associative add :=
  {assoc := add_assoc}

instance Commutative_add : Std.Commutative add :=
  {comm := add_comm}


theorem mul_add (l m n : ℕ) :
    mul l (add m n) = add (mul l m) (mul l n) :=
  by
    induction n with
    | zero        => rw[mul, add, add]
    | succ n' ih  => simp[mul, add, ih]; ac_rfl

end MyNats
