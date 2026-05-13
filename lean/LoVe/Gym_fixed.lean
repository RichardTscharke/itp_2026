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
