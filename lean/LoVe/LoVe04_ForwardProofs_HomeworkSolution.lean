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
  fun (a b : Prop) (hor : ¬ a ∨ b) (ha : a) ↦
    Or.elim hor (fun hna : ¬ a ↦ False.elim (hna ha)) (fun hb : b ↦ hb)

/- There are, in fact, two easy ways:

* Copy-paste the result of `#print about_Impl`.

* Simply enter `about_Impl` as the proof term for `about_Impl_term`. -/

/- 1.2. Prove the same theorem again, this time by providing a
structured proof, with `fix`, `assume`, and `show`. -/

theorem about_Impl_struct :
    ∀a b : Prop, ¬ a ∨ b → a → b :=
  fix a b : Prop
  assume hor : ¬ a ∨ b
  assume ha : a
  show b from
    Or.elim hor
      (assume hna : ¬ a
       show b from
         False.elim (hna ha))
      (assume hb : b
       show b from
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
  fun (a b : Prop) (habaab : (((a → b) → a) → a) → b) ↦
    habaab (fun habaa : (a → b) → a ↦
      habaa (fun ha : a ↦
        habaab (fun haba : (a → b) → a ↦
          ha)))

/- There are, in fact, three easy ways:

* Copy-paste the result of `#print weak_peirce`.

* Simply enter `weak_peirce` as the proof term for `weak_peirce_term`.

* Reuse the answer to question 1.2 of homework 1. -/

/- 2.2. Prove the same theorem again, this time by providing a structured
proof, with `fix`, `assume`, and `show`. -/

theorem weak_peirce_struct :
    ∀a b : Prop, ((((a → b) → a) → a) → b) → b :=
  fix a b : Prop
  assume habaab : (((a → b) → a) → a) → b
  show b from
    habaab
      (assume habaa : (a → b) → a
       show a from
         habaa
           (assume ha : a
            show b from
              habaab
                (assume haba : (a → b) → a
                  show a from
                    ha)))


/- ## Question 3: Connectives and Quantifiers

3.1. Supply a structured proof of the commutativity of `∧` under an `∃`
quantifier, using no other theorems than the introduction and elimination rules
for `∃`, `∧`, and `↔`. -/

theorem And_comm_under_Exists {α : Type} (p q : α → Prop) :
    (∃x, p x ∧ q x) ↔ (∃x, q x ∧ p x) :=
  Iff.intro
    (assume hex : ∃x, p x ∧ q x
     show ∃x, q x ∧ p x from
       Exists.elim hex
         (fix a : α
          assume hpq : p a ∧ q a
          have hp : p a :=
            And.left hpq
          have hq : q a :=
            And.right hpq
          show ∃x, q x ∧ p x from
            Exists.intro a (And.intro hq hp)))
    (assume hex : ∃x, q x ∧ p x
     show ∃x, p x ∧ q x from
       Exists.elim hex
         (fix a : α
          assume hqp : q a ∧ p a
          have hq : q a :=
            And.left hqp
          have hp : p a :=
            And.right hqp
          show ∃x, p x ∧ q x from
            Exists.intro a (And.intro hp hq)))

/- 3.2. Supply a structured proof of the commutativity of `∨` under a `∀`
quantifier, using no other theorems than the introduction and elimination rules
for `∀`, `∨`, and `↔`. -/

theorem Or_comm_under_All {α : Type} (p q : α → Prop) :
    (∀x, p x ∨ q x) ↔ (∀x, q x ∨ p x) :=
  Iff.intro
    (assume hall : ∀x, p x ∨ q x
     fix a : α
     show q a ∨ p a from
       Or.elim (hall a)
         (assume hp : p a
          Or.inr hp)
         (assume hq : q a
          Or.inl hq))
    (assume hall : ∀x, q x ∨ p x
     fix a : α
     show p a ∨ q a from
       Or.elim (hall a)
         (assume hq : q a
          Or.inr hq)
         (assume hp : p a
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
  assume h : DoubleNegation
  show Peirce from
    Peirce_of_EM (SorryTheorems.EM_of_DN h)

theorem EM_of_Peirce :
    Peirce → ExcludedMiddle :=
  assume h : Peirce
  show ExcludedMiddle from
    SorryTheorems.EM_of_DN (DN_of_Peirce h)

theorem dn_of_em :
    ExcludedMiddle → DoubleNegation :=
  assume h : ExcludedMiddle
  show DoubleNegation from
    DN_of_Peirce (Peirce_of_EM h)

end BackwardProofs

end LoVe
