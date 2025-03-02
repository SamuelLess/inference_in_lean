import InferenceInLean.A_Syntax
import InferenceInLean.B_Semantics
import InferenceInLean.C_Models
import InferenceInLean.D_Unification

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models
open Unification

/-! ### 3.7 Inference Systems and Proofs
In this section we define inferences and proofs, allowing us to define syntactic entailment and
soundness. -/

namespace Inferences

variable (sig : Signature) (X : Variables)

/-- We limit this to clausal proofs. -/
structure Inference where
  premises : Set (Clause sig X)
  conclusion : Clause sig X
  condition: Prop

abbrev InferenceSystem := List (Inference sig X)

instance : Membership (Inference sig X) (InferenceSystem sig X) :=
  List.instMembership

variable {sig : Signature} {X : Variables} {univ : Universes}

/-- This formalization of proofs is one of several possible translations for the definition in the
lecture notes, and is the one that ended up being the most ergonomic one to use for us. -/
structure Proof (Γ : InferenceSystem sig X) where
  assumptions : Set (Clause sig X)
  conclusion : Clause sig X
  clauses : List (Clause sig X)
  clauses_not_empty : clauses ≠ ∅
  last_clause_conclusion : clauses[clauses.length - 1]'(by
    exact Nat.sub_one_lt (by simp_all)) = conclusion
  is_valid : ∀ i (hindex : i < clauses.length), clauses[i] ∈ assumptions ∨
    ∃ inference ∈ Γ, clauses[i] = inference.conclusion ∧ inference.condition ∧
      ∀ Clause ∈ inference.premises, ∃ (j : ℕ) (hjindex : j < i), Clause = clauses[j]

/-- Syntactic entailment N ⊢ F in Γ. -/
@[simp]
def Provability (Γ : InferenceSystem sig X) (N : Set (Clause sig X)) (F : Clause sig X) : Prop :=
  ∃ proof : Proof Γ, proof.assumptions = N ∧ proof.conclusion = F

/-- This is the soundness definition from the lecture notes, which is based on inferences. -/
@[simp]
def Soundness [inst : DecidableEq X] (Γ : InferenceSystem sig X) : Prop :=
  ∀ inference ∈ Γ, inference.condition →
    @ClauseSetEntails _ _ univ _ inference.premises inference.conclusion

/-- This is the more general definition for soundness: An inference system Γ is sound if
N ⊢ F → N ⊨ F. -/
@[simp]
def GeneralSoundness [inst : DecidableEq X] (Γ : InferenceSystem sig X) : Prop :=
  ∀ (N : Set (Clause _ _)) (F : Clause _ _), Provability Γ N F → @ClauseSetEntails _ _ univ _ N F

/-- Proof that the more general definition of soundness follows from the inference-based one in
the lecture notes. This means that we can show the soundness of an inference system Γ just by
showing that all of its inferences are sound. -/
theorem generalSoundness_of_soundness [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : @Soundness _ _ univ _ Γ → @GeneralSoundness _ _ univ _ Γ := by
  /- The proof that was here before only worked due to a wrong definition of ClauseSetEntails.
  However, the proof was still correct at least for variables being the Empty type. -/
  sorry
