/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 4: Forward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Logic Puzzles

Consider the following tactical proof: -/

theorem about_Impl :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  by
    intros a b hor ha
    apply Or.elim hor
    · intro hna
      apply False.elim
      apply hna
      exact ha
    · intro hb
      exact hb

/- 1.1. Prove the same theorem again, this time by providing a proof term.

Hint: There is an easy way. -/

theorem about_Impl_term :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  -- about_Impl
  fun a => fun b => fun h!ab => fun ha : a =>
    (Or.elim h!ab
     (fun h!a => False.elim (h!a ha))
     (fun hb => hb))

/- 1.2. Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume h!ab : ¬ a ∨ b
  assume ha : a
  show b from
    Or.elim h!ab
      (assume h!a : a → False
       False.elim (h!a ha))
      (assume hb : b
       hb)


/- ## Question 2: More Logic Puzzles

Recall the following tactical proof: -/

theorem weak_peirce :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  by
    intro a b habaab
    apply habaab
    intro habaa
    apply habaa
    intro ha
    apply habaab
    intro haba
    apply ha

/- 2.1. Prove the same theorem again, this time by providing a proof
term.

Hint: There is an easy way. -/

theorem weak_peirce_term :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  -- weak_peirce
    fun (a b : Prop) ↦
      fun (habaab : (((a → b) → a) → a) → b) ↦
        habaab
          (fun (haba : (a → b) → a) ↦
            haba
              (fun (ha : a) ↦
                habaab
                  (fun (haba2 : (a → b) → a) ↦
                    ha)))

/- 2.2. Prove the same theorem again, this time by providing a structured
proof, with `fix`, `assume`, and `show`. -/

theorem weak_peirce_struct :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fix a b : Prop
  assume habaab : (((a → b) → a) → a) → b
  habaab
    (assume haba : (a → b) → a
     haba
      (assume ha : a
       habaab
        (assume haba2 : (a → b) → a
         ha)))


/- ## Question 3: Connectives and Quantifiers

3.1. Supply a structured proof of the commutativity of `∧` under an `∃`
quantifier, using no other theorems than the introduction and elimination rules
for `∃`, `∧`, and `↔`. -/

theorem And_comm_under_Exists {α : Type} (p q : α → Prop) :
    (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
  Iff.intro
    (assume hL : ∃ x, p x ∧ q x
     Exists.elim hL
      (fix a : α
       assume hpaqa : p a ∧ q a
       Exists.intro a
        (And.intro (And.right hpaqa) (And.left hpaqa))
      ))
    (assume hR : ∃x, q x ∧ p x
     Exists.elim hR
      (fix a : α
       assume hqapa : q a ∧ p a
       Exists.intro a
        (And.intro (And.right hqapa) (And.left hqapa))))

/- 3.2. Supply a structured proof of the commutativity of `∨` under a `∀`
quantifier, using no other theorems than the introduction and elimination rules
for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
    (assume hL : ∀x, p x ∨ q x
     fix x : α
     Or.elim (hL x)
      (assume hp : p x
       Or.inr hp)
      (assume hq : q x
       Or.inl hq))
    (assume hR : ∀x, q x ∨ p x
     fix x : α
     Or.elim (hR x)
      (assume hq : q x
       Or.inr hq)
      (assume hp : p x
       Or.inl hp))

/- 3.3. We have proved or stated three of the six possible implications between
`ExcludedMiddle`, `Peirce`, and `DoubleNegation` in the exercise of lecture 3.
Prove the three missing implications using structured proofs, exploiting the
three theorems we already have. -/

namespace BackwardProofs

#check Peirce_of_EM
#check DN_of_Peirce
#check SorryTheorems.EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  assume DN : DoubleNegation
  Peirce_of_EM (SorryTheorems.EM_of_DN DN)

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume Peirce : Peirce
  SorryTheorems.EM_of_DN (DN_of_Peirce Peirce)

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume EM : ExcludedMiddle
  DN_of_Peirce (Peirce_of_EM EM)

end BackwardProofs

end LoVe
