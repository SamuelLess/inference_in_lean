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
  intro hsound N F hprovable I hvalid β
  simp_all only [Soundness, ClauseSetEntails, Clause.eq_1, ValidIn, Assignment.eq_1, EntailsInterpret, Provability]
  obtain ⟨proof, hassumption, hconclusion⟩ := hprovable
  have hproofsequencetrue : ∀ F ∈ proof.clauses, EntailsInterpret I β F := by
    have hindicestrue : ∀ i (hindex : i < proof.clauses.length),
        EntailsInterpret I β proof.clauses[i] := by
      intro i hlen
      induction' i using Nat.case_strong_induction_on with i ih generalizing β
      · have hvalid := proof.is_valid 0 hlen
        aesop
      · have hvalid := proof.is_valid (i + 1) hlen
        rcases hvalid with hassump | hconseq
        · simp_all only [Assignment, EntailsInterpret]
        · rcases hconseq with ⟨inference, ⟨hin, ⟨hlast, hcond, hprev⟩⟩⟩
          rw [hlast]
          have hinfsound := hsound inference hin
          apply hinfsound
          · exact hcond
          · intro inf_form hprem
            have hinftrue := hprev inf_form hprem
            rcases hinftrue with ⟨j, ⟨hjindex, heq⟩⟩
            intro β
            have hjtrue := ih j (Nat.le_of_lt_succ hjindex) β (Nat.lt_trans hjindex hlen)
            rw [heq]
            exact hjtrue
    intro F hF
    have hfindex : ∃ (i : ℕ) (hindex : i < proof.clauses.length), proof.clauses[i] = F :=
      List.mem_iff_getElem.mp hF
    aesop
  have hlen : proof.clauses.length - 1 < proof.clauses.length := by
    have hlennonzero : proof.clauses.length ≠ 0 := by
      have hnonempty := proof.clauses_not_empty
      simp_all only [List.empty_eq, ne_eq, List.length_eq_zero_iff, not_false_eq_true]
    exact Nat.sub_one_lt hlennonzero
  have hfconclusion := proof.is_valid (proof.clauses.length - 1) hlen
  have hfislast : proof.clauses[proof.clauses.length - 1] = F := by
    rw [proof.last_clause_conclusion, hconclusion]
  rw [hfislast] at hfconclusion
  rcases hfconclusion with hl | hr
  · simp_all only [EntailsInterpret]
  · subst hfislast hassumption
    simp_all only [Clause.eq_1, EntailsInterpret, List.getElem_mem]
