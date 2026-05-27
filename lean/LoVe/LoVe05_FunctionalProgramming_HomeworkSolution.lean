/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe04_ForwardProofs_Demo
import LoVe.LoVe05_FunctionalProgramming_Demo


/- # LoVe Homework 5: Functional Programming

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Huffman Trees

Consider the following type of weighted binary trees: -/

inductive HTree (α : Type) where
  | leaf  : ℕ → α → HTree α
  | inner : ℕ → HTree α → HTree α → HTree α

/- Each constructor corresponds to a kind of node. An `HTree.leaf` node stores a
numeric weight and a label of some type `α`, and an `HTree.inner` node stores a
numeric weight, a left subtree, and a right subtree.

1.1. Define a polymorphic Lean function called `weight` that takes a
tree over some type variable `α` and that returns the weight component of the
root node of the tree: -/

def weight {α : Type} : HTree α → ℕ
  | HTree.leaf w _    => w
  | HTree.inner w _ _ => w

/- 1.2. Define a polymorphic Lean function called `unite` that takes
two trees `l, r : HTree α` and that returns a new tree such that (1) its left
child is `l`; (2) its right child is `r`; and (3) its weight is the sum of the
weights of `l` and `r`. -/

def unite {α : Type} : HTree α → HTree α → HTree α
  | l, r => HTree.inner (weight l + weight r) l r

/- 1.3. Consider the following `insort` function, which inserts a
tree `u` in a list of trees that is sorted by increasing weight and which
preserves the sorting. (If the input list is not sorted, the result is not
necessarily sorted.) -/

def insort {α : Type} (u : HTree α) : List (HTree α) → List (HTree α)
  | []      => [u]
  | t :: ts => if weight u ≤ weight t then u :: t :: ts else t :: insort u ts

/- Prove that `insort`ing a tree into a list cannot yield the empty list: -/

theorem insort_Neq_nil {α : Type} (t : HTree α) :
    ∀ts : List (HTree α), insort t ts ≠ []
  | []       => by simp [insort]
  | t' :: ts =>
    by
      cases Classical.em (weight t ≤ weight t') with
      | inl hw => simp [insort, hw]
      | inr hw => simp [insort, hw]

/- 1.4. Prove the same property as above again, this time as a
"paper" proof. Follow the guidelines given in question 1.4 of the exercise. -/

/- The proof is by case distinction (or induction) on `ts`.

Case `ts = []`. The goal is `insort t [] ≠ []`. We have
`insort t ts = [t] ≠ []`.

Case `ts = t' :: ts`. The goal is `insort t (t' :: ts) ≠ []`. We have
`insort t (t' :: ts) = if weight t ≤ weight t' then t :: t' :: ts else`
`t' :: insort ts`. If `weight t ≤ weight t'`, then we have
`insort t ts = t :: t' :: ts ≠ []` by distinctness of constructors. Otherwise,
we have `insort t ts = t' :: insort ts ≠ []`. QED -/


/- ## Question 2: Reverse of a List

Recall the `reverse` operation from lecture 2 and the `reverse_append` and
`reverse_reverse` theorems from the demo of lecture 4. -/

#check reverse
#check reverse_append
#check reverse_append_tactical
#check reverse_reverse

/- 2.1. Prove `reverse_append` again, this time using the calculational style
for the induction step. -/

theorem reverse_append_calc {α : Type} :
    ∀xs ys : List α, reverse (xs ++ ys) = reverse ys ++ reverse xs
  | [],      ys => by simp [reverse]
  | x :: xs, ys =>
    calc
      reverse (x :: xs ++ ys) = reverse (xs ++ ys) ++ [x] :=
        by rfl
      _ = reverse ys ++ reverse xs ++ [x] :=
        by simp [reverse_append_calc]
      _ = reverse ys ++ reverse (x :: xs) :=
        by simp [reverse]

/- 2.2. Prove the induction step in the proof below using the calculational
style, following this proof sketch:

      reverse (reverse (x :: xs))
    =     { by definition of `reverse` }
      reverse (reverse xs ++ [x])
    =     { using the theorem `reverse_append` }
      reverse [x] ++ reverse (reverse xs)
    =     { by the induction hypothesis }
      reverse [x] ++ xs
    =     { by definition of `++` and `reverse` }
      [x] ++ xs
    =     { by computation }
      x :: xs -/

theorem reverse_reverse_calc {α : Type} :
    ∀xs : List α, reverse (reverse xs) = xs
  | []      => by rfl
  | x :: xs =>
    calc
      reverse (reverse (x :: xs)) = reverse (reverse xs ++ [x]) :=
        by rw [reverse]
      _ = reverse [x] ++ reverse (reverse xs) :=
        by rw [reverse_append]
      _ = reverse [x] ++ xs :=
        by rw [reverse_reverse_calc xs]
      _ = [x] ++ xs :=
        by simp [reverse]
      _ = x :: xs :=
        by rfl


/- ## Question 3: Gauss's Summation Formula

`sumUpToOfFun f n = f 0 + f 1 + ⋯ + f n`: -/

def sumUpToOfFun (f : ℕ → ℕ) : ℕ → ℕ
  | 0     => f 0
  | m + 1 => sumUpToOfFun f m + f (m + 1)

/- 3.1. Prove the following theorem, discovered by Carl Friedrich Gauss as a
pupil.

Hints:

* The `mul_add` and `add_mul` theorems might be useful to reason about
  multiplication.

* The `linarith` tactic introduced in lecture 6 might be useful to reason about
  addition. -/

#check mul_add
#check add_mul

theorem sumUpToOfFun_eq :
    ∀m : ℕ, 2 * sumUpToOfFun (fun i ↦ i) m = m * (m + 1)
  | 0     => by rfl
  | m + 1 =>
    by
      simp [sumUpToOfFun, sumUpToOfFun_eq m, add_mul, mul_add]
      linarith

/- 3.2. Prove the following property of `sumUpToOfFun`. -/

theorem sumUpToOfFun_mul (f g : ℕ → ℕ) :
    ∀n : ℕ, sumUpToOfFun (fun i ↦ f i + g i) n =
      sumUpToOfFun f n + sumUpToOfFun g n
  | 0     => by rfl
  | n + 1 =>
    by
      simp [sumUpToOfFun, sumUpToOfFun_mul _ _ n]
      ac_rfl

/- 3.3. Prove `sumUpToOfFun_mul` again as a "paper" proof. Follow the
guidelines given in question 1.4 of the exercise. -/

/- We perform the proof by structural induction on `n`.

Case 0: The goal is `sumUpToOfFun (fun i ↦ f i + g i) 0 =`
`sumUpToOfFun f 0 + sumUpToOfFun g 0`. The left-hand side equals `0` by
definition of `sumUpToOfFun`. Similarly, the right-hand side equals `0 + 0`,
i.e., `0`.

Case `n' + 1`. The goal is `sumUpToOfFun (fun i ↦ f i + g i) (n' + 1) =`
`sumUpToOfFun f (n' + 1) + sumUpToOfFun g (n' + 1)`. The induction hypothesis is
`sumUpToOfFun (fun i ↦ f i + g i) n' = sumUpToOfFun f n' + sumUpToOfFun g n'`.

Let us simplify the goal's left-hand side:

      sumUpToOfFun (fun i ↦ f i + g i) (n' + 1)
    = sumUpToOfFun (fun i ↦ f i + g i) n' + (f (n' + 1) + g (n' + 1))
      -- by definition of `sumUpToOfFun`
    = sumUpToOfFun f n' + sumUpToOfFun g n' + (f (n' + 1) + g (n' + 1))
      -- by the induction hypothesis

Now let us massage the right-hand side so that it matches the simplified
left-hand side:

      sumUpToOfFun f (n' + 1) + sumUpToOfFun g (n' + 1)
    = (sumUpToOfFun f n' + f (n' + 1)) + (sumUpToOfFun g n' + g (n' + 1))
      -- by definition of `sumUpToOfFun` (twice)
    = sumUpToOfFun f n' + sumUpToOfFun g n' + (f (n' + 1) + g (n' + 1))
      -- by associativity and commutativity of `+`

The two sides are equal. QED -/

end LoVe
