/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe03_BackwardProofs_ExerciseSheet


/- # LoVe Homework 3: Backward Proofs

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe

namespace BackwardProofs


/- ## Question 1: Connectives and Quantifiers

1.1. Complete the following proofs using basic tactics such as `intro`,
`apply`, and `exact`.

Hint: Some strategies for carrying out such proofs are described at the end of
Section 3.3 in the Hitchhiker's Guide. -/

theorem B (a b c : Prop) :
    (a → b) → (c → a) → c → b :=
  by
    intro hab hca hc
    apply hab
    apply hca
    exact hc

theorem S (a b c : Prop) :
    (a → b → c) → (a → b) → a → c :=
  by
    intro habc hab ha
    apply habc
    · exact ha
    · apply hab
      exact ha

theorem nonsense1 (a b c d : Prop) :
    ((a → b) → c → d) → c → b → d :=
  by
    intro h hc hb
    apply h
    · intro ha
      exact hb
    · exact hc

theorem nonsense2 (a b c : Prop) :
    (a → b) → (a → c) → a → b → c :=
  by
    intro hab hac ha hb
    clear hab hb
    apply hac
    exact ha

theorem nonsense3 (a b c : Prop) :
    (c → (a → b) → a) → c → b → a :=
  by
    intro h hc hb
    apply h
    · assumption
    · intro ha
      assumption

theorem nonsense4 (a b c : Prop) :
    (a → a → b) → (b → c) → a → b → c :=
  by
    intro haab hbc ha hb
    clear haab ha
    apply hbc
    apply hb

/- 1.2. Prove the following theorem using basic tactics. -/

theorem weak_peirce (a b : Prop) :
    ((((a → b) → a) → a) → b) → b :=
  by
    intro habaab
    apply habaab
    intro haba
    apply haba
    intro ha
    apply habaab
    intro haba
    exact ha


/- ## Question 2: Logical Connectives

2.1. Prove the following property about double negation using basic tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `False` at a key point in the
  proof. -/

theorem herman (a : Prop) :
    ¬¬ (¬¬ a → a) :=
  by
    intro h!
    apply h!
    intro h!!a
    apply False.elim
    apply h!!a
    intro ha
    apply h!
    intro h!!a
    exact ha

/- 2.2. Prove the following property about implication using basic tactics.

Hints:

* Keep in mind that `¬ a` is defined as `a → False`. You can start by invoking
  `simp [Not]` if this helps you.

* You will need to apply the elimination rule for `∨` and `False` at some point
  in the proof. -/

theorem about_Impl (a b : Prop) :
    ¬ a ∨ b → a → b :=
  by
    intro h
    intro ha
    apply Or.elim h
    · intro h!a
      apply False.elim
      apply h!a
      exact ha
    · intro hb
      exact hb


/- 2.3. Prove the missing link in our chain of classical axiom implications.

Hints:

* One way to find the definitions of `DoubleNegation` and `ExcludedMiddle`
  quickly is to

  1. hold the Control (on Linux and Windows) or Command (on macOS) key pressed;
  2. move the cursor to the identifier `DoubleNegation` or `ExcludedMiddle`;
  3. click the identifier.

* You can use `rw DoubleNegation` to unfold the definition of
  `DoubleNegation`, and similarly for the other definitions.

* You will need to apply the double negation hypothesis for `a ∨ ¬ a`. You will
  also need the left and right introduction rules for `∨` at some point. -/

#check DoubleNegation
#check ExcludedMiddle

theorem EM_of_DN :
    DoubleNegation → ExcludedMiddle :=
  by
    rw[DoubleNegation, ExcludedMiddle]
    intro hDN a
    apply hDN
    intro h!
    apply h!
    apply Or.inr
    intro ha
    apply h!
    apply Or.inl
    exact ha


/- 2.4. We have proved three of the six possible implications between
`ExcludedMiddle`, `Peirce`, and `DoubleNegation`. State and prove the three
missing implications, exploiting the three theorems we already have. -/

#check Peirce_of_EM
#check DN_of_Peirce
#check EM_of_DN

theorem Peirce_of_DN :
    DoubleNegation → Peirce :=
  by
    intro hDN
    apply Peirce_of_EM
    apply EM_of_DN
    assumption

theorem DN_of_EM :
    ExcludedMiddle → DoubleNegation :=
  by
    intro hEM
    apply DN_of_Peirce
    apply Peirce_of_EM
    exact hEM

theorem EM_of_Pierce :
    Peirce → ExcludedMiddle :=
  by
    intro hP
    apply EM_of_DN
    apply DN_of_Peirce
    exact hP


end BackwardProofs

end LoVe
