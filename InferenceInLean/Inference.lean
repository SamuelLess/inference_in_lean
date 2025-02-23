import InferenceInLean.Syntax
import InferenceInLean.Semantics
import InferenceInLean.Models
import InferenceInLean.Unification

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models
open Unification
namespace Inferences
/-
### 3.7 Inference Systems and Proofs
-/

/--
We limit this to clausal proofs.
-/
structure Inference (sig : Signature) (X : Variables) where
  premises : Set (Clause sig X)
  conclusion : Clause sig X
  condition: Prop

def InferenceSystem (sig : Signature) (X : Variables) := List (Inference sig X)

instance {sig : Signature} {X : Variables} : Membership (Inference sig X) (InferenceSystem sig X) :=
  List.instMembership

structure Proof {sig : Signature} {X : Variables} (Γ : InferenceSystem sig X) where
  assumptions : Set (Clause sig X)
  conclusion : Clause sig X
  clauses : List (Clause sig X)
  clauses_not_empty : clauses ≠ ∅
  last_clause_conclusion : clauses[clauses.length - 1]'(by
    have hlennonzero : clauses.length ≠ 0 := by
      simp_all only [List.empty_eq, ne_eq, List.length_eq_zero, not_false_eq_true]
    exact Nat.sub_one_lt hlennonzero) = conclusion
  is_valid : ∀ i (hindex : i < clauses.length), clauses[i] ∈ assumptions ∨
    ∃ inference ∈ Γ, clauses[i] = inference.conclusion ∧ inference.condition ∧
      ∀ Clause ∈ inference.premises, ∃ (j : ℕ) (hjindex : j < i), Clause = clauses[j]

@[simp]
def Provability {sig : Signature} {X : Variables}
    (Γ : InferenceSystem sig X) (N : Set (Clause sig X)) (F : Clause sig X) : Prop :=
  ∃ proof : Proof Γ, proof.assumptions = N ∧ proof.conclusion = F

@[simp]
def Soundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Prop :=
  ∀ inference ∈ Γ, inference.condition → ClauseSetEntails inference.premises inference.conclusion

@[simp]
def GeneralSoundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Prop :=
  ∀ (N : Set (Clause sig X)) (F : Clause sig X), Provability Γ N F → ClauseSetEntails N F

theorem generalSoundness_of_soundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Soundness Γ → GeneralSoundness Γ := by
  intro hsound N F hproof A β hgstrue
  rcases hproof with ⟨proof, ⟨hassumptions, hconclusion⟩⟩
  have hproofsequencetrue : ∀ F ∈ proof.clauses, EntailsInterpret A β F := by
    have hindicestrue : ∀ i (hindex : i < proof.clauses.length),
        EntailsInterpret A β proof.clauses[i] := by
      intro i hlen
      induction' i using Nat.case_strong_induction_on with i ih
      · have hvalid := proof.is_valid 0 hlen
        aesop
      · have hvalid := proof.is_valid (i + 1) hlen
        rcases hvalid with hassump | hconseq
        · simp_all only [Soundness, SetEntails, Assignment, EntailsInterpret]
        · rcases hconseq with ⟨inference, ⟨hin, ⟨hlast, hcond, hprev⟩⟩⟩
          rw [hlast]
          have hinfsound := hsound inference hin
          apply hinfsound
          · exact hcond
          · intro inf_form hprem
            have hinftrue := hprev inf_form hprem
            rcases hinftrue with ⟨j, ⟨hjindex, heq⟩⟩
            have hjtrue := ih j (Nat.le_of_lt_succ hjindex) (Nat.lt_trans hjindex hlen)
            rw [heq]
            exact hjtrue
    intro F hF
    have hfindex : ∃ (i : ℕ) (hindex : i < proof.clauses.length), proof.clauses[i] = F :=
      List.mem_iff_getElem.mp hF
    aesop
  have hlen : proof.clauses.length - 1 < proof.clauses.length := by
    have hlennonzero : proof.clauses.length ≠ 0 := by
      have hnonempty := proof.clauses_not_empty
      simp_all only [List.empty_eq, ne_eq, List.length_eq_zero, not_false_eq_true]
    exact Nat.sub_one_lt hlennonzero
  have hfconclusion := proof.is_valid (proof.clauses.length - 1) hlen
  have hfislast : proof.clauses[proof.clauses.length - 1] = F := by
    rw [proof.last_clause_conclusion, hconclusion]
  rw [hfislast] at hfconclusion
  rcases hfconclusion with hl | hr
  · simp_all only [Soundness, SetEntails, Assignment, EntailsInterpret]
  · subst hassumptions hconclusion
    obtain ⟨inference, h⟩ := hr
    obtain ⟨hinf, right⟩ := h
    obtain ⟨hconcs, hcond, hforms⟩ := right
    have h := hsound inference hinf
    rw [hconcs]
    apply h
    · exact hcond
    · intro G hgprem
      have hinf := hforms G hgprem
      rcases hinf with ⟨j, hjnotconc, hginforms⟩
      simp_all only [Soundness, SetEntails, Assignment, EntailsInterpret,
        implies_true, List.getElem_mem]
