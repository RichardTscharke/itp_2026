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
One of the advantages of using the predefined binds is
  that it provides syntactic sugar, the >>= operator:
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

The term   bind ma f   executes ma >>= f a, where a is the unboxed result of ma.


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

3. (ma >>= f) >>= g = ma >>= (fun a ↦ f a >>= g)
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

Type Classes are constructs parameterized by a type, for monoids by  m : Type → Type
Whenever we use a field from the type class (e.g. pure, bind)
  on a concrete m (e.g. Option, List),
  the type class inference mechanism retrieves the relevant structure value.
-/
class LawMonad (m : Type → Type) extends Pure m, Bind m where
  pure_bind {α β : Type} (a : α) (f : α → m β)  : pure a >>= f = f a
  bind_pure {α : Type} (ma : m α)               : ma >>= pure = ma
  bind_assoc {α β γ : Type} (ma : m α) (f : α → m β) (g : β → m γ) :
    (ma >>= f ) >>= g = ma >>= (fun a ↦ f a >>= g)
/-
To instantiate this definition, we must supply:
* the type constructor m : Type → Type
* suitable bind and pure operators (bind, pure)
* proofs of the laws (pure_bind, bind_pure, bind_assoc)
-/

/-
## 7.4 No Effects

We want to register Lean’s constant id {α: Type} : α → α as a monad:
-/
def id.pure {α : Type} : α → id α
  | a => a

def id.bind {α β : Type} : id α → (α → id β) → id β
  | ma, f => f ma

instance id.LawMonad : LawMonad id :=
  {
    pure := id.pure
    bind := id.bind

    pure_bind :=
      by
        intro α β a f
        rw[pure, bind]

    bind_pure :=
      by
        intro α ma
        rw[bind, pure]

    bind_assoc :=
      by
        intro α β γ ma f g
        simp[bind]
  }
/-
The registration process requires the pure and bind operators and proofs of the three laws.
-/

/-
## 7.5 Basic Exceptions

We register the Option moand:
-/
def Option.pure {α : Type} : α → Option α :=
  Option.some

def Option.bind {α β : Type} : Option α → (α → Option β) → Option β
  | Option.none, _    => Option.none
  | Option.some x, f  => f x

instance Option.LawMonad : LawMonad Option :=
  {
    pure := Option.pure
    bind := Option.bind

    pure_bind :=
      by
        intro α β a f
        rfl

    bind_pure :=
      by
        intro α ma
        cases ma with
        | none   => rfl
        | some x => rfl

    bind_assoc :=
      by
        intro α β γ ma f g
        cases ma with
        | none    => simp[bind]
        | some x  => simp[bind]
  }
/-
Beyond the standard operations, it can be useful to throw and catch exceptions:
-/
def Option.throw {α : Type} : Option α :=
  Option.none

def Option.catch {α : Type} : Option α → Option α → Option α
  | Option.none, ma'  => ma'
  | Option.some a, _  => Option.some a

/-
* Option.throw leaves the program in an error state (throw exception)
* The Option.catch operation
  | leaves the program at is, if Option.some
  | executes the alternative program if Option.none
    -> second argument acts as "exception-handling code"

The Option monad only handles one type of error
-/


/-
## 7.6 Mutable State

def welcomeNewUser (userName : String) (ctxt : Context) :
    (ℕ × String) × Context :=
  let
    (userId, ctxt’) := createUser userName ctxt
    (password, ctxt’’) := generateTemporaryPassword userId ctxt’
    (ok, ctxt’’’) := sendUnencryptedEmail user password ctxt’’
  in
    ((userId, password), ctxt’’’)

input: some global state or context ctxt
* invokes three functions in turn, each of which takes a context value
* returns both some data and a new context
* The context is effectively threaded through the program
* This allows us to have a mutable state in a programming language
    without side effects.

Simplified:

def welcomeNewUserDo (userName : String) : Context → (N × String) × Context :=
  do
    let user      ← createUser userName
    let password  ← generateTemporaryPassword user
    let ok        ← sendUnencryptedEmail user password
    pure (user, password)

The state monad provides this desired syntax and logic.
It builds on top of a binary type constructor **Action**.
Action captures the concept of computations (actions) over
  states of type σ with return values of type α.
-/
def Action (σ α : Type) : Type :=
  σ → α × σ
/-
For a given type σ, (Action σ) : Type → Type is a monad.
The type σ represents the memory over the universe/context (e.g. lists, tupels)

* σ → gives the old state
* α × gives the result of the computation
* × σ gives the new state

As with other effectful programs, the do notation
  only exposes the data (the value of type α)
  and conceals the effect (the old and new σ states).

If σ := Unit (the type whos only value is () ), Action Unit corresponds to id.
Thus, the type Unit → α × Unit is isomorphic to α
-/

-- reads a state, adds it as the result, and leaves the state as is
def Action.read {σ : Type} : Action σ σ
  | s => (s, s)

-- writes an input s as the new state without computational results
def Action.write {σ : Type} (s : σ) : Action σ Unit
  | _ => ((), s)

def Action.pure {α σ : Type} : α → Action σ α
  | x, s => (x, s)

def Action.bind {α β σ : Type} : Action σ α → (α → Action σ β) → Action σ β
  | ma, f, s => match ma s with
                | (a, s') => f a s'
