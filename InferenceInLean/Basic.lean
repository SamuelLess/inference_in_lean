import InferenceInLean.Syntax
import InferenceInLean.Semantics
import InferenceInLean.Models
import InferenceInLean.Unification
import InferenceInLean.Inference

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics
open Models
open Unification
open Inferences

namespace Resolution

/-
### 3.8 Ground (or Propositional) Resolution
-/

@[simp]
def GroundResolutionRule {sig : Signature} (A : Atom sig Empty) (C D : Clause sig Empty) :
    Inference sig Empty :=
  ⟨{.pos A :: C, .neg A :: D}, C.append D, True⟩

@[simp]
def GroundFactorizationRule {sig : Signature} (A : Atom sig Empty) (C : Clause sig Empty) :
    Inference sig Empty :=
  ⟨{.pos A :: .pos A :: C}, .pos A :: C, True⟩

/--
Both rules of the Resolution Calculus.
Note that at the moment this is an inference system.
Ideally we could somehow move the `A C D` inside the rules to use factorization without `D`.
-/
@[simp]
def GroundResolution (sig : Signature) (A : Atom sig Empty) (C D : Clause sig Empty) :
    InferenceSystem sig Empty :=
  [GroundResolutionRule A C D, GroundFactorizationRule A C]

lemma ground_clause_iff_literal {sig: Signature}
    (I : Interpretation sig) (β : Assignment Empty I.univ) (C : Clause sig Empty) :
    Formula.eval I β ↑C ↔ (∃ L ∈ C, Literal.satisfied_by L I β) ∨ C = [] := by
  apply Iff.intro
  · intro h_eval
    induction C with
    | nil => simp
    | cons head tail ih =>
      left
      by_cases hl : Literal.satisfied_by head I β
      · use head
        simp_all only [Clause, Literal.satisfied_by, EntailsInterpret, List.mem_cons, true_or,
          and_self]
      · sorry -- show that ¬head.sat ∨ .eval ↑(head :: tail) → .eval ↑tail using `false_or`
  · sorry -- this should be the easier case using induction on C and `List.mem_cons`

theorem groundResolution_soundness {sig : Signature }
    {A : Atom sig Empty} {C D : Clause sig Empty} : Soundness (GroundResolution sig A C D):= by
  rw [Soundness]
  intro rule h_rule_ground I β h_premise_true
  simp [EntailsInterpret]
  simp_all only [GroundResolution, GroundResolutionRule, Clause, List.append_eq, GroundFactorizationRule,
    EntailsInterpret]
  rw [List.mem_cons, List.mem_singleton] at h_rule_ground
  cases h_rule_ground
  -- proof of resolution rule
  next h_res_rule =>
    subst h_res_rule
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    obtain ⟨h_posAconsC, h_negAconsD⟩ := h_premise_true
    have := (ground_clause_iff_literal I β (Literal.pos A :: C)).mp h_posAconsC
    sorry -- the heavy lifting here should be done by `ground_clause_iff_literal`
  -- proof of factorization rule
  next h_fact_rule =>
    subst h_fact_rule
    simp_all only [Clause, Set.mem_singleton_iff, Clause.toFormula, Formula.eval, Atom.eval,
      or_self_left, forall_eq]


/-
### 3.10 General Resolution
-/

-- TODO: do we need to add that freeVars ∩ freeVars = ∅?
@[simp]
def GeneralResolutionRule {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (A B : Atom sig X) (C D : Clause sig X) :
    Inference sig X :=
  ⟨{.pos A :: C, .neg B :: D}, C.append D, ∃ σ : Substitution sig X, MostGeneralUnifier [(A, B)] σ⟩

@[simp]
def GeneralFactorizationRule {sig : Signature} {X : Variables} [inst : DecidableEq X]
  (A B : Atom sig X) (C : Clause sig X) :
    Inference sig X :=
  ⟨{.pos A :: .pos B :: C}, .pos A :: C, ∃ σ : Substitution sig X, MostGeneralUnifier [(A, B)] σ⟩



theorem generalResolution_soundness {sig : Signature } {X : Variables} [inst : DecidableEq X]
    {A B : Atom sig X} {C D : Clause sig X} :
    Soundness ([GeneralResolutionRule A B C D, GeneralFactorizationRule A B C]):= by
  sorry


/-
## Further stuff:
- Compactness

-/
