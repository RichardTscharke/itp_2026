import LoVe.LoVelib
set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unnecessarySeqFocus false
set_option linter.tacticAnalysis.introMerge false

namespace Effectful

/-
# 7. Effectful Programming

Monads generalize programs with effects.
In Lean, they are used to express imperative programs and to reason about them.
-/

def nth {α : Type} : List α → ℕ → Option α
  | [], _         => Option.none
  | (x :: xs), 0  => Option.some x
  | (x :: xs), n  => nth xs (n - 1)

#eval nth [1,2,3] 2

def sum_2_5_7 (xs : List ℕ) : Option ℕ :=
  match nth xs 1 with
    | Option.none => Option.none
    | Option.some n₂ =>
        match nth xs 4 with
          |Option.none => Option.none
          | Option.some n₅ =>
              match nth xs 6 with
                | Option.none => Option.none
                | Option.some n₇ => Option.some (n₂ + n₅ + n₇)

#eval sum_2_5_7 [1,2,3,4,5,6,7,8]

/-
The **connect** function works on an Option.
If the value is Option.none, we leave it as is.
Otherwise, the value is of the form Option.some a,
  and we apply the operation f on a or bind f’s argument to a.
-/
def connect {α β : Type} : Option α → (α → Option β) → Option β
  | Option.none, _    => Option.none
  | Option.some x, f  => f x

def sum257_connect (xs : List ℕ) : Option ℕ :=
  connect (nth xs 1)
    (fun n₂ ↦ connect (nth xs 4)
      (fun n₅ ↦ connect (nth xs 6)
        (fun n₇ ↦ n₂ +n₅ + n₇)))

/-
Lean has a predefined bind function that does the same as our connect:
-/
def sum257_bind (ns : List ℕ) : Option ℕ :=
  bind (nth ns 1)
    (fun n₂ ↦ bind (nth ns 4)
       (fun n₅ ↦ bind (nth ns 6)
          (fun n₇ ↦ pure (n₂ + n₅ + n₇))))

/-
One of the advantages of using the predefined bindis that it provides syntactic
sugar, in the form of the >>= operator:
-/
def sum257_sugar (xs : List ℕ) : Option ℕ :=
  (nth xs 1) >>= (fun n₂ ↦ (nth xs 4) >>= (fun n₅ ↦ (nth xs 6) >>= (fun n₇ ↦ n₂ + n₅ + n₇)))

/-
The **do**-notation provides a convenient syntax for effectful programs.
The program   do let a ← oa ... is equivalent to oa >>= (fun a → ...)
-/
def sum257_do (xs : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth xs 1
    do
      let n₅ ← nth xs 4
      do
        let n₇ ← nth xs 6
        n₂ + n₅ + n₇

/-
The do notation conveniently also allows multiple let bindings in a single block:
-/
def sum257_do₂ (xs : List ℕ) : Option ℕ :=
  do
    let n₂ ← nth xs 1
    let n₅ ← nth xs 4
    let n₇ ← nth xs 6
    n₂ + n₅ + n₇


/-
## 7.2 Two Operations and Three Laws

In general, a monad is a unary type constructor m : Type → Type
equipped with two distinguished operations:

* pure {α : Type} : α → m α                     (embeds a pure, effectless program)
* bind {α β : Type} : m α → (α → m β) → m β     (composes two effectful programs)

The term   bind ma f   executes ma and then executes f a, where a is the unboxed result of ma.


The bind and pure operations are normally required to obey three laws.

The bind operation combines two programs.
If either of these is a pure program, we can inline it and eliminate the bind.
This gives us the first two laws:

1. pure a >>= f = f a
do
  let a' ← pure a
  f a'
=
f a

2. ma >>= pure = ma
do
  let a ← ma
  pure a
=
ma

The third law is an associativity rule for bind. It allows us to flatten a nested
computation:
3.
do
  let b ←
    do
      let a ← ma
      f a
    g b
=
do
  let a ← ma
  let b ← f a
  g b
-/


/-
## 7.3 A Type Class

Type Classes are constructs parameterized by a type, here by  m : Type → Type
Whenever we use a field from the type class (e.g. pure, bind)
  on a concrete m (e.g. Option, List),
  the type class inference mechanism retrieves the relevant structure value.
-/
class LawMonad (m : Type → Type) extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β)  : pure a >>= f = f a
  bind_pure {α : Type} (ma : m α)               : ma >>= pure = ma
  bind_assoc {α β γ : Type} (ma : m α) (f : α → m β) (g : β → m γ)
    : (ma >>= f) >>= g = ma >>= (fun a ↦ f a >>= g)
/-
To instantiate this definition, we must supply:
* the type constructor m : Type → Type
* suitable bind and pure operators (bind, pure)
* proofs of the laws (pure_bind, bind_pure, bind_assoc)
-/

/-
## 7.4 No Effects
-/
