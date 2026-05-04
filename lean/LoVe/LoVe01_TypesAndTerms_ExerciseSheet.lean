/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe01_TypesAndTerms_Demo


/- # LoVe Exercise 1: Types and Terms

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Terms

Complete the following definitions, by replacing the `sorry` markers by terms
of the expected type.

Hint: A procedure for doing so systematically is described in Section 1.4 of
the Hitchhiker's Guide. As explained there, you can use `_` as a placeholder
while constructing a term. By hovering over `_`, you will see the current
logical context. -/

def I : α → α :=
  fun a ↦ a

def K : α → β → α :=
  fun a b ↦ a

def C : (α → β → γ) → β → α → γ :=
  fun f b a ↦ f a b

def projFst : α → α → α :=
  fun a b ↦ a

/- Give a different answer than for `projFst`. -/

def projSnd : α → α → α :=
  fun a b ↦ b

def someNonsense : (α → β → γ) → α → (α → γ) → β → γ :=
  /- fun f a g b ↦ g a -/
  fun f a g b ↦ f a b


/- ## Question 2: Typing Derivation

Show the typing derivation for your definition of `C` above, on paper or using
ASCII or Unicode art. Start with an empty context. You might find the
characters `–` (to draw horizontal bars) and `⊢` useful. -/

/-
------------------------------------------- VAR  ------------------------------------ VAR
f : α → β → γ, b : β, a : α ⊢ f : α → β → γ      f : α → β → γ, b : β, a : α ⊢ a : α
------------------------------------------- APP  ------------------------------------ APP     ------------------------------------ VAR
                      f : α → β → γ, b : β, a : α ⊢ f a : β → γ                               f : α → β → γ, b : β, a : α ⊢ b : β
                      ------------------------------------------ APP                          ------------------------------------ APP
                                                        f : α → β → γ, b : β, a : α ⊢ f a b : γ
                                                ----------------------------------------------------- FUN
                                                f : α → β → γ, b : β ⊢ (fun (a : α) ↦ f a b) : α → γ
                                            ---------------------------------------------------------- FUN
                                            f : α → β → γ ⊢ (fun (b : β) (a : α) ↦ f a b) : β → α → γ
                                      -------------------------------------------------------------------------- FUN
                                      ⊢ (fun (f : α → β → γ) (b : β) (a : α) ↦ f a b) : (α → β → γ) → β → α → γ
-/

end LoVe
