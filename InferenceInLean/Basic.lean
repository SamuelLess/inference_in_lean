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

/- ### 3.8 Ground Resolution -/

namespace Resolution

variable {sig : Signature} {X : Variables} {univ : Universes}

@[simp]
def GroundResolutionRule (A : Atom sig Empty) (C D : Clause sig Empty) : Inference sig Empty :=
  ⟨{.pos A :: C, .neg A :: D}, C ++ D, True⟩

@[simp]
def GroundFactorizationRule (A : Atom sig Empty) (C : Clause sig Empty) : Inference sig Empty :=
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

lemma eval_append_iff_eval_or [DecidableEq X]
    {I : Interpretation sig univ} (β : Assignment X univ) (C D : Clause sig X):
    Formula.eval I β (↑(C ++ D)) ↔
    Formula.eval I β (Formula.or ↑C ↑D) := by
  induction' C with c cs ih generalizing D
  · simp only [Clause, List.nil_append, Formula.eval, Clause.toFormula, Formula.eval.eq_1, false_or]
  · match c with
    | .pos a =>
      specialize ih D
      rw [List.cons_append, Clause.toFormula]
      rw [Clause.toFormula, Formula.eval] at *
      rw [ih]
      aesop
    | .neg a =>
      rw [Clause.toFormula]
      specialize ih D
      rw [List.cons_append, Clause.toFormula]
      rw [Formula.eval] at *
      rw [ih]
      aesop

theorem groundResolution_soundness {A : Atom sig Empty} {C D : Clause sig Empty} :
    @Soundness _ _ univ _ (GroundResolution sig A C D):= by
  intro rule h_rule_ground hcond I β h_premise_true
  simp [EntailsInterpret]
  simp_all only [GroundResolution, GroundResolutionRule, Clause, List.append_eq,
    GroundFactorizationRule, EntailsInterpret]
  rw [List.mem_cons, List.mem_singleton] at h_rule_ground
  cases h_rule_ground
  -- proof of resolution rule
  next h_res_rule =>
    subst h_res_rule
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, forall_eq]
    obtain ⟨h_posAconsC, h_negAconsD⟩ := h_premise_true
    rw [eval_append_iff_eval_or]
    aesop
  -- proof of factorization rule
  next h_fact_rule =>
    subst h_fact_rule
    simp_all only [Clause, Set.mem_singleton_iff, Clause.toFormula, Formula.eval, Atom.eval,
      or_self_left, forall_eq]

/- ### 3.10 General Resolution -/

-- TODO: do we need to add that freeVars ∩ freeVars = ∅?
@[simp]
def GeneralResolutionRule [inst : DecidableEq X] (A B : Atom sig X) (C D : Clause sig X) :
    Inference sig X :=
  ⟨{.pos A :: C, .neg B :: D}, C ++ D, ∃ σ : Substitution sig X, MostGeneralUnifier [(A, B)] σ⟩

@[simp]
def GeneralFactorizationRule [inst : DecidableEq X] (A B : Atom sig X) (C : Clause sig X) :
    Inference sig X :=
  ⟨{.pos A :: .pos B :: C}, .pos A :: C, ∃ σ : Substitution sig X, MostGeneralUnifier [(A, B)] σ⟩

theorem generalResolution_soundness [inst : DecidableEq X] {A B : Atom sig X} {C D : Clause sig X} :
    @Soundness _ _ univ _ ([GeneralResolutionRule A B C D, GeneralFactorizationRule A B C]):= by
  rw [Soundness]
  intro rule h_rule_ground hcond I β h_premise_true
  simp_all only [GeneralResolutionRule, Clause, List.append_eq, GeneralFactorizationRule,
    EntailsInterpret]
  rw [List.mem_cons, List.mem_singleton] at h_rule_ground
  cases h_rule_ground
  -- proof of resolution rule
  next h_res_rule =>
    subst h_res_rule
    simp only [GeneralResolutionRule] at h_premise_true
    simp_all only [Clause, GeneralResolutionRule, List.append_eq, Substitution.eq_1,
      MostGeneralUnifier, Unifier, Equality.eq_1, EqualityProblem.eq_1, List.mem_singleton,
      forall_eq, MoreGeneral, Set.mem_insert_iff, Set.mem_singleton_iff,
      EntailsInterpret, forall_eq_or_imp, Clause.toFormula, Formula.eval]
    rcases hcond with ⟨σ, hunif, hmgu⟩
    clear hmgu
    sorry
  next h_fact_rule =>
    sorry


/-
## Further stuff:
- Compactness

-/
