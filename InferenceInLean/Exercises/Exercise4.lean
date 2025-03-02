import InferenceInLean.F_Resolution
import Mathlib.Data.Finset.Defs

set_option autoImplicit false

open Syntax
open Semantics
open Models
open Unification
open Inferences

variable {sig : Signature} {X : Variables} {univ : Universes}

/- ## Exercise 4 -/

namespace Exercise4

/- ### Exercise 4-1 -/

namespace Task1

inductive fs where | b | c | d | f deriving BEq
inductive ps where | P
def F : Formula ⟨fs, ps⟩ String := .and (.and (.and (.atom (.pred .P [.func .b []]))
  (.atom (.pred .P [.func .c []])))
  (.neg (.atom (.pred .P [.func .d []]))))
  (.neg (.ex "x" (.atom (.pred .P [.func .f [.func .f [.var "x"]]]))))

theorem ex_4_1 : ∃ I : Interpretation ⟨fs, ps⟩ (Fin 2), ∃ β : Assignment String (Fin 2),
    Formula.eval I β F := by
  let I : Interpretation ⟨fs, ps⟩ (Fin 2) := ⟨
    fun g a => if g == .f || g == .d then 1 else 0,
    fun _ u => if u[0]! == 0 then True else False⟩
  use I
  use (fun _ => 0)
  simp [I, F]
  have : fs.f == fs.f := rfl
  aesop

end Task1


/- ### Exercise 4-2 -/

namespace Task2

/- ! Rather large chunks of this namespace were generated by Claude 3.7 Sonnet (free version) !
  This worked somewhat well, the largest parts of the actual proofs were wrong though. -/

inductive funs where | plus | succ | zero deriving BEq

inductive preds where | eq deriving BEq

@[simp]
def sig42 : Signature := ⟨funs, preds⟩

@[simp]
def term_plus (t₁ t₂ : Term sig42 String) : Term sig42 String :=
  Term.func funs.plus [t₁, t₂]

@[simp]
def term_succ (t : Term sig42 String) : Term sig42 String :=
  Term.func funs.succ [t]

@[simp]
def term_zero : Term sig42 String :=
  Term.func funs.zero []

@[simp]
def atom_eq (t₁ t₂ : Term sig42 String) : Atom sig42 String :=
  Atom.pred preds.eq [t₁, t₂]

-- F₁ = ∀x (x + 0 ≈ x)
@[simp]
def F₁ : Formula sig42 String :=
  Formula.all "x" (
    Formula.atom (
      atom_eq
        (term_plus (Term.var "x") term_zero)
        (Term.var "x")))

-- F₂ = ∀x∀y (x + s(y) ≈ s(x + y))
@[simp]
def F₂ : Formula sig42 String :=
  Formula.all "x" (
    Formula.all "y" (
      Formula.atom (
        atom_eq
          (term_plus (Term.var "x") (term_succ (Term.var "y")))
          (term_succ (term_plus (Term.var "x") (Term.var "y"))))))

-- F₃ = ∀x∀y (x + y ≈ y + x)
@[simp]
def F₃ : Formula sig42 String :=
  Formula.all "x" (
    Formula.all "y" (
      Formula.atom (
        atom_eq
          (term_plus (Term.var "x") (Term.var "y"))
          (term_plus (Term.var "y") (Term.var "x")))))

-- F₄ = ¬∀x∀y (x + y ≈ y + x)
@[simp]
def F₄ : Formula sig42 String :=
  Formula.neg F₃

/- Part (a): Model of F₁, F₂, F₃ -/
theorem ex_4_2a : ∃ I : Interpretation sig42 (Fin 2), ∃ β : Assignment String (Fin 2),
    Formula.eval I β (.and (.and F₁ F₂) F₃) := by
  let I : Interpretation sig42 (Fin 2) := ⟨
    fun f args => match f with
      | .plus => (args[0]! + args[1]!) % 2
      | .succ => (args[0]! + 1) % 2
      | .zero => 0,
    fun _ args => args[0]! = args[1]!⟩

  use I
  use (fun _ => 0)
  simp [I, F₁, F₂, F₃]

  -- Prove F₁: ∀x (x + 0 ≈ x)
  have h₁ : ∀ (x : Fin 2), (x + 0) % 2 = x := by aesop

  -- Prove F₂: ∀x∀y (x + s(y) ≈ s(x + y))
  have h₂ : ∀ (x y : Fin 2), (x + ((y + 1) % 2)) % 2 = ((x + y) % 2 + 1) % 2 := by
    aesop (add norm Fin.add_def)

  -- Prove F₃: ∀x∀y (x + y ≈ y + x)
  have h₃ : ∀ (x y : Fin 2), (x + y) % 2 = (y + x) % 2 := by
    intro x y
    simp_all only [Fin.isValue, Fin.add_zero, I, Fin.add_def]
    rw [Nat.add_comm]

  simp_all only [Fin.add_zero, I]
  simp_all only [Fin.isValue, Nat.add_mod_mod, implies_true, true_and, I]


/- Part (b): Model of F₁, F₂, F₄ -/
theorem ex_4_2b : ∃ I : Interpretation sig42 (Fin 2), ∃ β : Assignment String (Fin 2),
    Formula.eval I β (.and (.and F₁ F₂) F₄) := by
  -- Define non-commutative interpretation
  let I : Interpretation sig42 (Fin 2) := ⟨
    -- Function interpretations
    fun f args => match f with
      | .plus => match args[0]!, args[1]! with
        | 0, 0 => 0
        | 1, 0 => 1
        | 0, 1 => 0
        | 1, 1 => 0
      | .succ => args[0]!  -- Identity function for successor
      | .zero => 0,
    fun _ args => args[0]! = args[1]!⟩
  use I
  use (fun _ => 0)
  simp [I, F₁, F₂, F₄]

  apply And.intro
  · aesop
  · use 0
    use 1
    exact Fin.zero_ne_one

end Task2


end Exercise4
