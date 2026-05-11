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
