/- Copyright © 2018–2026 Anne Baanen, Alexander Bentkamp, Jasmin Blanchette,
Xavier Généreux, Johannes Hölzl, and Jannis Limperg. See `LICENSE.txt`. -/

import LoVe.LoVe06_InductivePredicates_Demo


/- # LoVe Homework 12: Logical Foundations of Mathematics

Replace the placeholders (e.g., `:= sorry`) with your solutions. -/


set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace LoVe


/- ## Question 1: Even Numbers as a Subtype

Usually, the most convenient way to represent even natural numbers is to use the
larger type `ℕ`, which also includes the odd natural numbers. If we want to
quantify only over even numbers `n`, we can add an assumption `Even n` to our
theorem statement.

An alternative is to encode evenness in the type, using a subtype. We will
explore this approach.

1.1. Define the type `Eveℕ` of even natural numbers, using the `Even` predicate
introduced in the lecture 5 demo. -/

#print Even

def Eveℕ : Type :=
  {n : ℕ // Even n}

/- 1.2. Prove the following theorem about the `Even` predicate. You will need
it to answer question 1.3.

Hint: The theorems `add_assoc` and `add_comm` might be useful. -/

theorem Even.add {m n : ℕ} (hm : Even m) (hn : Even n) :
    Even (m + n) :=
  by
    induction hm with
    | zero            => simp [*]
    | add_two k hk ih =>
      rw [add_assoc]
      rw [add_comm 2 n]
      rw [← add_assoc]
      apply Even.add_two
      apply ih

/- 1.3. Define zero and addition of even numbers by filling in the `sorry`
placeholders. -/

def Eveℕ.zero : Eveℕ :=
  Subtype.mk 0 Even.zero

def Eveℕ.add (m n : Eveℕ) : Eveℕ :=
  Subtype.mk (Subtype.val m + Subtype.val n)
    (Even.add (Subtype.property m) (Subtype.property n))

/- 1.4. Prove that addition of even numbers is commutative and associative, and
has 0 as an identity element. -/

theorem Eveℕ.add_comm (m n : Eveℕ) :
    Eveℕ.add m n = Eveℕ.add n m :=
  by
    apply Subtype.eq
    simp [Eveℕ.add]
    ac_rfl

theorem Eveℕ.add_assoc (l m n : Eveℕ) :
    Eveℕ.add (Eveℕ.add l m) n = Eveℕ.add l (Eveℕ.add m n) :=
  by
    apply Subtype.eq
    simp [Eveℕ.add]
    ac_rfl

theorem Eveℕ.add_iden_left (n : Eveℕ) :
    Eveℕ.add Eveℕ.zero n = n :=
  by
    apply Subtype.eq
    simp [Eveℕ.zero, Eveℕ.add]

theorem Eveℕ.add_iden_right (n : Eveℕ) :
    Eveℕ.add n Eveℕ.zero = n :=
  by rw [Eveℕ.add_comm, Eveℕ.add_iden_left]


/- ## Question 2: Multisets as a Quotient Type

A multiset (or bag) is a collection of elements that allows for multiple
(but finitely many) occurrences of its elements. For example, the multiset
`{2, 7}` is equal to the multiset `{7, 2}` but different from `{2, 7, 7}`.

Finite multisets can be defined as a quotient over lists. We start with the
type `List α` of finite lists and consider only the number of occurrences of
elements in the lists, ignoring the order in which elements occur. Following
this scheme, `[2, 7, 7]`, `[7, 2, 7]`, and `[7, 7, 2]` would be three equally
valid representations of the multiset `{2, 7, 7}`.

The `List.count` function returns the number of occurrences of an element in a
list. Since it uses equality on elements of type `α`, it requires `α` to belong
to the `BEq` (Boolean equality) type class. For this reason, the definitions and
theorems below all take `[BEq α]` as type class argument.

2.1. Provide the missing proof below. -/

instance Multiset.Setoid (α : Type) [BEq α] : Setoid (List α) :=
  { r     := fun as bs ↦ ∀x, List.count x as = List.count x bs
    iseqv :=
      { refl  :=
          by simp
        symm  :=
          by aesop
        trans :=
          by aesop
      } }

/- 2.2. Define the type of multisets as the quotient over the relation
`Multiset.Setoid`. -/

def Multiset (α : Type) [BEq α] : Type :=
  Quotient (Multiset.Setoid α)

/- 2.3. Now we have a type `Multiset α` but no operations on it. Basic
operations on multisets include the empty multiset (`∅`), the singleton
multiset (`{x} `for any element `x`), and the sum of two multisets (`A ⊎ B` for
any multisets `A` and `B`). The sum should be defined so that the
multiplicities of elements are added; thus, `{2} ⊎ {2, 2} = {2, 2, 2}`.

Fill in the `sorry` placeholders below to implement the basic multiset
operations. -/

def Multiset.mk {α : Type} [BEq α] : List α → Multiset α :=
  Quotient.mk (Multiset.Setoid α)

def Multiset.empty {α : Type} [BEq α] : Multiset α :=
  Multiset.mk []

def Multiset.singleton {α : Type} [BEq α] (a : α) : Multiset α :=
  Multiset.mk [a]

def Multiset.union {α : Type} [BEq α] : Multiset α → Multiset α → Multiset α :=
  Quotient.lift₂
    (fun as bs ↦ Multiset.mk (as ++ bs))
    (by
       intro as bs as' bs' ha hb
       apply Quotient.sound
       intro x
       simp [ha x, hb x])

/- 2.4. Prove that `Multiset.union` is commutative and associative
and has `Multiset.empty` as identity element. -/

theorem Multiset.union_comm {α : Type} [BEq α] (A B : Multiset α) :
    Multiset.union A B = Multiset.union B A :=
  by
    induction A using Quotient.inductionOn with
    | h as =>
      induction B using Quotient.inductionOn with
      | h bs =>
        apply Quotient.sound
        intro x
        simp [add_comm]

theorem Multiset.union_assoc {α : Type} [BEq α] (A B C : Multiset α) :
    Multiset.union (Multiset.union A B) C =
    Multiset.union A (Multiset.union B C) :=
  by
    induction A using Quotient.inductionOn with
    | h as =>
      induction B using Quotient.inductionOn with
      | h bs =>
        induction C using Quotient.inductionOn with
        | h cs =>
          apply Quotient.sound
          intro x
          simp

theorem Multiset.union_iden_left {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union Multiset.empty A = A :=
  by
    induction A using Quotient.inductionOn with
    | h as =>
      apply Quotient.sound
      intro x
      simp

theorem Multiset.union_iden_right {α : Type} [BEq α] (A : Multiset α) :
    Multiset.union A Multiset.empty = A :=
  by
    rw [Multiset.union_comm]
    rw [Multiset.union_iden_left]


/- ## Question 3: Hilbert Choice

3.1. Prove the following theorem.

Hints:

* A good way to start is to make a case distinction on whether `∃n, f n < x`
  is true or false.

* The theorem `le_of_not_gt` might be useful. -/

theorem exists_minimal_arg_helper (f : ℕ → ℕ) :
    ∀x m, f m = x → ∃n, ∀i, f n ≤ f i
  | x, m, eq =>
    by
      cases Classical.em (∃n, f n < x) with
      | inl hex =>
        cases hex with
        | intro n hn =>
          apply exists_minimal_arg_helper _ (f n) n
          rfl
      | inr hnex =>
        apply Exists.intro m
        rw [eq]
        intro n
        apply le_of_not_gt
        intro hx
        apply hnex
        apply Exists.intro n
        exact hx

/- Now this interesting theorem falls off: -/

theorem exists_minimal_arg (f : ℕ → ℕ) :
    ∃n : ℕ, ∀i : ℕ, f n ≤ f i :=
  exists_minimal_arg_helper f _ 0 (by rfl)

/- 3.2. Use what you learned about Hilbert choice in the lecture to define the
following function, which returns the (or an) index of the minimal element in
`f`'s image. -/

noncomputable def minimal_arg (f : ℕ → ℕ) : ℕ :=
  Classical.choose (exists_minimal_arg f)

/- 3.3. Prove the following characteristic theorem about your definition. -/

theorem minimal_arg_spec (f : ℕ → ℕ) :
    ∀i : ℕ, f (minimal_arg f) ≤ f i :=
  Classical.choose_spec (exists_minimal_arg f)


/- ## Question 4: Nonempty Types

In the lecture, we saw the inductive predicate `Nonempty` that states that a
type has at least one element: -/

#print Nonempty

/- The purpose of this question is to think about what would happen if all
types had at least one element. To investigate this, we introduce this fact as
an axiom as follows. Introducing axioms should be generally avoided or done
with great care, since they can easily lead to contradictions, as we will
see. -/

axiom Sort_Nonempty (α : Sort _) :
    Nonempty α

/- This axiom gives us a theorem `Sort_Nonempty` admitted with no proof. It
resembles a theorem proved by `sorry`, but without the warning. -/

#check Sort_Nonempty

/- 4.1. Prove that this axiom leads to a contradiction, i.e., lets us derive
`False`. -/

theorem first_proof_of_False :
    False :=
  Classical.choice (Sort_Nonempty False)

/- 4.2. Prove that even the following weaker axiom leads to a contradiction,
without using the axiom or the theorem from question 4.1.

Hint: Subtypes can help. -/

axiom Type_Nonempty (α : Type _) :
    Nonempty α

theorem second_proof_of_False :
    False :=
  by
    let t : Type := {a : ℕ // False}
    have h : Nonempty t :=
      Type_Nonempty t
    let x : t := Classical.choice h
    exact Subtype.property x

end LoVe
