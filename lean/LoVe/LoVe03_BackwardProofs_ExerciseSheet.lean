/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_Demo


/- # LoVe Exercise 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Carry out the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem I (a : Prop) :
    a → a :=
  by
    intro ha
    exact ha

theorem K (a b : Prop) :
    a → b → b :=
  by
    intro ha hb
    clear ha
    exact hb

theorem C (a b c : Prop) :
    (a → b → c) → b → a → c :=
  by
    intro habc hb ha
    apply habc
    · exact ha
    · exact hb

theorem proj_fst (a : Prop) :
    a → a → a :=
  by
    intro ha haa
    exact ha

/- Please give a different answer than for `proj_fst`: -/

theorem proj_snd (a : Prop) :
    a → a → a :=
  by
    intro ha haa
    exact haa

theorem some_nonsense (a b c : Prop) :
    (a → b → c) → a → (a → c) → b → c :=
  by
    intro habc ha hac hb
    clear habc hb
    apply hac
    exact ha

/- 1.2. Prove the contraposition rule using basic tactics. -/

theorem contrapositive (a b : Prop) :
    (a → b) → ¬ b → ¬ a :=
  by
    intro hab h!b ha
    apply False.elim
    apply h!b
    apply hab
    exact ha



/- 1.3. Prove the distributivity of `∀` over `∧` using basic tactics.

Hint: This exercise is tricky, especially the right-to-left direction. Some
forward reasoning, like in the proof of `and_swap_braces` in the lecture, might
be necessary. -/

theorem forall_and {α : Type} (p q : α → Prop) :
    (∀x, p x ∧ q x) ↔ (∀x, p x) ∧ (∀x, q x) :=
  by
    apply Iff.intro
    · intro hApq
      apply And.intro
      · intro x
        exact And.left (hApq x)
      · intro x
        exact And.right (hApq x)
    · intro hApAq x
      apply And.intro
      · exact And.left hApAq x
      · exact And.right hApAq x


/- ## Question 2: Natural Numbers

2.1. Prove the following recursive equations on the first argument of the
`mul` operator defined in lecture 1. -/

#check mul
/-
def mul : Nat → Nat → Nat
  | _, .zero    => .zero
  | m, .succ n  => add m (mul m n)
-/

theorem mul_zero (n : ℕ) :
    mul 0 n = 0 :=
  by
    induction n with
    | zero        => rw[mul]
    | succ n' ih  => rw[mul, ih, add]

#check add_succ
theorem mul_succ (m n : ℕ) :
    mul (Nat.succ m) n = add (mul m n) n :=
  by
    induction n with
    | zero        => rw[mul, mul, add]
    | succ n' ih  => simp[mul, add, ih, add_succ, add_assoc]

/- 2.2. Prove commutativity and associativity of multiplication using the
`induction` tactic. Choose the induction variable carefully. -/

theorem mul_comm (m n : ℕ) :
    mul m n = mul n m :=
  by
    induction n with
    | zero        => rw[mul_zero, mul]
    | succ n' ih  => rw[mul, mul_succ, ih, add_comm]

theorem mul_assoc (l m n : ℕ) :
    mul (mul l m) n = mul l (mul m n) :=
  by
    induction n with
    | zero        => simp[mul]
    | succ n' ih  => simp[mul, mul_add, ih]

/- 2.3. Prove the symmetric variant of `mul_add` using `rw`. To apply
commutativity at a specific position, instantiate the rule by passing some
arguments (e.g., `mul_comm _ l`). -/

theorem add_mul (l m n : ℕ) :
    add (mul n l) (mul n m) = mul (add l m) n :=
  by
    induction n with
    | zero        => simp[mul, mul_zero]
                     rfl
    | succ n' ih  => rw[mul_comm (add l m) _, mul_add]


/- ## Question 3 (**optional**): Intuitionistic Logic

Intuitionistic logic is extended to classical logic by assuming a classical
axiom. There are several possibilities for the choice of axiom. In this
question, we are concerned with the logical equivalence of three different
axioms: -/

def ExcludedMiddle : Prop :=
  ∀a : Prop, a ∨ ¬ a

def Peirce : Prop :=
  ∀a b : Prop, ((a → b) → a) → a

def DoubleNegation : Prop :=
  ∀a : Prop, (¬¬ a) → a

/- For the proofs below, avoid using theorems from Lean's `Classical` namespace.

3.1 (**optional**). Prove the following implication using tactics.

Hint: You will need `Or.elim` and `False.elim`. You can use
`rw [ExcludedMiddle]` to unfold the definition of `ExcludedMiddle`,
and similarly for `Peirce`. -/

theorem Peirce_of_EM :
    ExcludedMiddle → Peirce :=
  by
    rw[ExcludedMiddle, Peirce]
    intro hEM
    intro a b
    intro haba
    apply Or.elim (hEM a)
    · intro ha
      exact ha
    · intro h!a
      apply haba
      intro ha
      apply False.elim
      apply h!a
      apply ha


/- 3.2 (**optional**). Prove the following implication using tactics. -/

theorem DN_of_Peirce :
    Peirce → DoubleNegation :=
  by
    rw[Peirce, DoubleNegation]
    intro hP a h!!a
    apply hP a False
    intro h!a
    apply False.elim
    apply h!!a
    exact h!a

/- We leave the remaining implication for the homework: -/

namespace SorryTheorems

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    rw[DoubleNegation, ExcludedMiddle]
    intro hDN a
    apply hDN (a ∨ ¬ a)
    intro h
    apply h
    apply Or.inr
    intro ha
    apply h
    apply Or.inl ha


end SorryTheorems

end BackwardProofs

end LoVe
