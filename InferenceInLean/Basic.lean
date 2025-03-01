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

lemma eval_append_iff_eval_or_subst [DecidableEq X] {I : Interpretation sig univ}
    (β : Assignment X univ) (C D : Clause sig X) (σ : Substitution sig X):
    Formula.eval I β ↑((C ++ D).substitute σ) ↔
    Formula.eval I β (Formula.or ↑(C.substitute σ) ↑(D.substitute σ)) := by
  induction' C with c cs ih generalizing D
  · simp_all only [Clause.substitute, Clause, List.nil_append, Formula.eval, List.map_nil,
      Clause.toFormula, false_or]
  · match c with
    | .pos a => aesop
    | .neg a => aesop

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

lemma validclosed_of_valid [DecidableEq X] {C: Clause sig X} {I : Interpretation sig univ} :
    ValidIn C.toFormula I → ValidIn C.toClosedFormula I := by
  intro heval
  let xs := C.freeVarsList
  let n := xs.length
  have hxsnodup : xs.Nodup := by exact nodup_clauseFreeVarsList sig X _
  have := (@three_three_seven sig X univ _ n C I xs hxsnodup rfl).mpr
  exact fun β => this heval β

/- Direct formalization of Proposition 3.10.14 -/
theorem generalResolutionRuleSound [DecidableEq X] (A B : Atom sig X) (C D : Clause sig X)
    (σ : Substitution sig X) (hmgu : MostGeneralUnifier [(A, B)] σ) :
    @Entails _ _ univ _
      (Formula.and
        (Clause.toClosedFormula sig X (.pos B :: D))
        (Clause.toClosedFormula sig X (.neg A :: C)))
      (((D ++ C).substitute σ).toClosedFormula) := by
  let leftinner : Clause sig X := (.pos B :: D)
  let rightinner : Clause sig X := (.neg A :: C)
  let left := Clause.toClosedFormula sig X (.pos B :: D)
  let right := Clause.toClosedFormula sig X (.neg A :: C)
  intro I β h_entails
  simp [Formula.and] at h_entails
  obtain ⟨hleft, hright⟩ := h_entails
  have hleftentails : EntailsInterpret I β left := by exact hleft
  have hrightentails : EntailsInterpret I β right := by exact hright
  have hleftclosed : Formula.closed left := by
    exact Clause.closedClause_closed sig X (Literal.pos B :: D)
  have hrightclosed : Formula.closed right := by
    exact Clause.closedClause_closed sig X (Literal.neg A :: C)
  have hleftvalid : ValidIn left I := validIn_of_entails_closed I _ hleftclosed (by use β)
  have hrightvalid : ValidIn right I := validIn_of_entails_closed I _ hrightclosed (by use β)

  -- ∀z (D ∨ B)σ
  let leftxs : List X := leftinner.freeVarsList
  let leftn : ℕ := leftxs.length
  have hleftxsnodup : leftxs.Nodup := by exact nodup_clauseFreeVarsList sig X leftinner

  let leftys : List X := (leftinner.substitute σ).freeVarsList
  let leftm : ℕ := leftys.length
  have hleftysnodup : leftys.Nodup := by
    exact nodup_clauseFreeVarsList sig X (Clause.substitute σ leftinner)

  have hleft338 := @three_three_eight univ sig X _
    leftinner I σ leftn leftm leftxs leftys hleftxsnodup rfl hleftysnodup rfl hleftvalid

  --∀z (C ∨ ¬A)σ
  let rightxs : List X := rightinner.freeVarsList
  let rightn : ℕ := rightxs.length
  have hrightxsnodup : rightxs.Nodup := by exact nodup_clauseFreeVarsList sig X rightinner

  let rightys : List X := (rightinner.substitute σ).freeVarsList
  let rightm : ℕ := rightys.length
  have hrightysnodup : rightys.Nodup := by
    exact nodup_clauseFreeVarsList sig X (Clause.substitute σ rightinner)

  have hright338 := @three_three_eight univ sig X _
    rightinner I σ rightn rightm rightxs rightys hrightxsnodup rfl hrightysnodup rfl hrightvalid

  -- use 3.3.7
  have hleftinnersub : @ValidIn _ X _ _ (leftinner.substitute σ) I := by
    exact (three_three_seven leftys.length
      (Clause.toFormula sig X (Clause.substitute σ leftinner)) I leftys hleftysnodup rfl).mp
      hleft338

  have hrightinnersub : @ValidIn _ X _ _ (rightinner.substitute σ) I := by
    exact (three_three_seven rightys.length
      (Clause.toFormula sig X (Clause.substitute σ rightinner)) I rightys hrightysnodup rfl).mp
      hright338

  have hDσ_of_negBσ : ∀ β : Assignment X univ, ¬Atom.eval I β (B.substitute σ) →
      Formula.eval I β (D.substitute σ) := by
    intro β' hnegatom
    simp [*] at hleftinnersub
    unfold leftinner at hleftinnersub
    have heval_leftinnersub := hleftinnersub β'
    simp [List.map_cons] at heval_leftinnersub
    rcases heval_leftinnersub with hBσ | hDσ
    · simp_all only [Atom.substitute, Atom.pred.injEq, Atom.eval, List.map_map, not_true_eq_false]
    · exact hDσ

  have hCσ_of_Aσ : ∀ β : Assignment X univ, Atom.eval I β (A.substitute σ) →
      Formula.eval I β (C.substitute σ) := by
    intro β' hatom
    simp [*] at hrightinnersub
    unfold rightinner at hrightinnersub
    have heval_rightinnersub := hrightinnersub β'
    simp [List.map_cons] at heval_rightinnersub
    rcases heval_rightinnersub with hnAσ | hCσ
    · simp only [Atom.eval, Atom.substitute, List.map_map, hnAσ] at hatom
    · exact hCσ

  have hBσeqAσ: ∀ (β : Assignment X univ), Atom.eval I β (A.substitute σ)
      = Atom.eval I β (B.substitute σ) := by
    intro β
    have hunif : A.substitute σ = B.substitute σ := by
      obtain ⟨hσunif, _⟩ := hmgu
      simp only [Unifier, EqualityProblem.eq_1, List.mem_singleton, Atom.substitute,
        Atom.pred.injEq, forall_eq] at hσunif
      simp only [Atom.substitute, Atom.pred.injEq]
      exact hσunif
    rw [hunif]

  have hCDσ : ∀ β' : Assignment X univ, EntailsInterpret I β' (Clause.substitute σ (D ++ C)) := by
    intro β'
    by_cases hBσ : Atom.eval I β' (B.substitute σ)
    · have hAσ : Atom.eval I β' (A.substitute σ) := by
        rw [hBσeqAσ]
        exact hBσ
      have hCσ := hCσ_of_Aσ β' hAσ
      unfold Clause.substitute at hCσ
      simp only [EntailsInterpret, Clause.substitute, Clause, List.map_append]
      generalize List.map (Literal.substitute σ) D = D'
      generalize List.map (Literal.substitute σ) C = C' at *
      apply (@eval_append_iff_eval_or sig X univ _ I β' D' C').mpr
      aesop
    · have hDσ := hDσ_of_negBσ β' hBσ
      unfold Clause.substitute at hDσ
      simp only [EntailsInterpret, Clause.substitute, Clause, List.map_append]
      generalize List.map (Literal.substitute σ) D = D' at *
      generalize List.map (Literal.substitute σ) C = C'
      apply (@eval_append_iff_eval_or sig X univ _ I β' D' C').mpr
      aesop

  exact validclosed_of_valid hCDσ β
