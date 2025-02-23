import InferenceInLean.Syntax
import InferenceInLean.Semantics
import InferenceInLean.Models

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models
namespace Unification

/-
### Unification
-/

@[simp]
def Equality (sig : Signature) (X : Variables) :=
  Atom sig X × Atom sig X

@[simp]
def EqualityProblem (sig : Signature) (X : Variables) :=
  List (Equality sig X)

instance {sig : Signature} {X : Variables} : Membership (Equality sig X) (EqualityProblem sig X) :=
  List.instMembership

@[simp]
def EqualityProblem.freeVars {sig : Signature} {X : Variables} :
    @EqualityProblem sig X -> Set X
  | [] => ∅
  | (lhs, rhs) :: eqs => Atom.freeVars lhs ∪ Atom.freeVars rhs ∪ freeVars eqs

@[simp]
def Unifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : @EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  ∀ eq ∈ E, have ⟨lhs, rhs⟩ := eq; lhs.substitute σ = rhs.substitute σ

def example_unification_problem : EqualityProblem (Signature.mk String String) String :=
  [(.pred "P" [.func "f" [Term.var "x"]], .pred "P" [Term.var "y"])]

def example_unifier : Substitution (Signature.mk String String) String :=
  fun x => if x == "y" then Term.func "f" [Term.var "x"] else Term.var x

theorem example_unification : Unifier example_unification_problem example_unifier := by
  simp [example_unification_problem, example_unifier]

@[simp]
def MostGeneralUnifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  Unifier E σ ∧ (∀ τ : Substitution sig X, Unifier E τ → σ ≤ τ)

/-
TODO: Add example proof for a mgu.
-/

lemma mgu_imp_unifier {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X)
    (σ : Substitution sig X) : MostGeneralUnifier E σ → Unifier E σ := fun ⟨h, _⟩ => h

@[simp]
def Unifiable {sig : Signature} {X : Variables} [DecidableEq X]
  (E : EqualityProblem sig X) : Prop := ∃ σ : Substitution sig X, Unifier E σ

theorem unifiable_iff_mgu_idempot {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (E : EqualityProblem sig X) : Unifiable E ↔ ∃ σ : Substitution sig X,
      MostGeneralUnifier E σ ∧ Idempotent σ ∧ σ.domain ∪ σ.codomain ⊆ E.freeVars := by
  apply Iff.intro
  · sorry -- this will need the standard unification algorithm
  · intro h
    obtain ⟨σ, ⟨⟨⟩⟩⟩ := h
    use σ
alias main_unification_theorem := unifiable_iff_mgu_idempot
