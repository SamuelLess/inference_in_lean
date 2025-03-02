import InferenceInLean.A_Syntax
import InferenceInLean.B_Semantics

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics

/-! ## 3.3 Models, Validity, and Satisfiability
In this section we establish various notions of semantic entailment and prove several lemmas that
show how assignments and substitutions interact. -/

namespace Models

variable {sig : Signature} {X : Variables} {univ : Universes}

/- ### Truth and Validity -/

/-- I,β ⊨ F -/
@[simp]
def EntailsInterpret [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (F : Formula sig X) : Prop :=
  Formula.eval I β F

theorem not_entails_not [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (F : Formula sig X) :
    EntailsInterpret I β F → ¬EntailsInterpret I β (Formula.neg F) :=
  fun a a_1 ↦ a_1 a

/-- F is true/valid in I: I ⊨ F -/
@[simp]
def ValidIn [DecidableEq X] (F : Formula sig X) (I : Interpretation sig univ) : Prop :=
  ∀ (β : Assignment X univ), EntailsInterpret I β F

/-- Tautology: ⊨ F -/
@[simp]
def Valid [DecidableEq X] (F : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ), Formula.eval I β F

/- ### Entailment -/

/-- Semantic entailment: F ⊨ G -/
@[simp]
def Entails [DecidableEq X] (F G : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ),
    EntailsInterpret I β F → EntailsInterpret I β G
infix:60 " ⊨ " => Entails

/-- F ⊨ G ↔ ⊨ F → G -/
theorem entails_iff_imp_valid [inst : DecidableEq X]
    (F G : Formula sig X) : @Entails _ _ univ _ F G ↔ @Valid _ _ univ _ (Formula.imp F G) :=
  Eq.to_iff rfl

/- N ⊨ F -/
@[simp]
def SetEntails [DecidableEq X]
    (N : Set (Formula sig X)) (F : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ),
    (∀ G ∈ N, EntailsInterpret I β G) → EntailsInterpret I β F

@[simp]
def ClauseSetEntails [DecidableEq X]
    (N : Set <| Clause sig X) (C : Clause sig X) : Prop :=
  ∀ (I : Interpretation sig univ),
    (∀ D ∈ N, @ValidIn _ X _ _ D I) → @ValidIn _ X _ _ C I

lemma entails_setEntails [inst : DecidableEq X]
    (F G : Formula sig X) : @Entails _ _ univ _ F G ↔ @SetEntails _ X univ _ {F} G := by simp

/- ### Satsfiability -/

@[simp]
def Satisfiable [DecidableEq X] (F : Formula sig X) : Prop :=
  ∃ (I : Interpretation sig univ) (β : Assignment X univ), EntailsInterpret I β F

@[simp]
def Unsatisfiable [DecidableEq X] (F : Formula sig X) : Prop :=
  ¬@Satisfiable _ X univ _ F

theorem valid_iff_not_unsat [inst : DecidableEq X]
    (F : Formula sig X) : @Valid _ _ univ _ F ↔ @Unsatisfiable _ _ univ _ (Formula.neg F) := by simp

theorem entails_iff_and_not_unsat [inst : DecidableEq X] (F G : Formula sig X) :
    @Entails _ _ univ _ F G ↔ @Unsatisfiable _ _ univ _ (Formula.and F (Formula.neg G)) := by simp

@[simp]
def Literal.satisfied_by [DecidableEq X]
    (L : Literal sig X) (I : Interpretation sig univ) (β : Assignment X univ) : Prop :=
  EntailsInterpret I β <| match L with
    | Literal.pos a => Formula.atom a
    | Literal.neg a => Formula.neg (Formula.atom a)

@[simp]
def ClauseSatisfiable [DecidableEq X] (C : Clause sig X) : Prop :=
  ∃ (I : Interpretation sig univ) (β : Assignment X univ),
    ∃ L : Literal sig X, L ∈ C ∧ Literal.satisfied_by L I β

@[simp]
theorem ClauseSatisfiable_imp_Satisfiable [inst : DecidableEq X]
    (C : Clause sig X) : @ClauseSatisfiable _ _ univ _ C → @Satisfiable sig X univ _ ↑C := by
  simp only [ClauseSatisfiable, Assignment, Satisfiable, EntailsInterpret]
  intro ⟨I, ⟨β, ⟨L, ⟨h_L_in_C, hsatby⟩⟩⟩⟩
  use I, β
  induction C with
  | nil =>
    exact False.elim (List.not_mem_nil L h_L_in_C)
  | cons head Ctail ih =>
    rw [Clause.toFormula.eq_def]
    split
    next => simp_all only [Literal.satisfied_by, EntailsInterpret, Clause.eq_1, List.not_mem_nil]
    all_goals -- proof cases for Literal.pos and Literal.neg at once
    next h_split atom tail h_head_pos_atom =>
      simp_all only [List.cons.injEq, Formula.eval]
      obtain ⟨h_head_atom, _⟩ := h_head_pos_atom
      have mem_head : L = head ∨ L ∈ tail := by simp [h_head_atom, List.mem_cons.mp h_L_in_C]
      cases mem_head
      next _h_is_head =>
        constructor
        simp_all only [List.cons.injEq, true_and, Atom.eval]
        exact hsatby
      next h_in_tail =>
        apply Or.inr
        exact ih h_in_tail

@[simp]
def SetSatisfiable [DecidableEq X] (N : Set (@Formula sig X)) : Prop :=
  ∃ (I : Interpretation sig univ) (β : Assignment X univ), ∀ G ∈ N, EntailsInterpret I β G

@[simp]
def ClauseSetSatisfiableByLiterals [DecidableEq X] (N : Set <| Clause sig X) : Prop :=
  ∃ (I : Interpretation sig univ) (β : Assignment X univ),
    ∀ C ∈ N, ∃ L ∈ C, Literal.satisfied_by L I β

@[simp]
def ClauseSetSatisfiable [DecidableEq X] (N : Set <| Clause sig X) : Prop :=
  ∃ (I : Interpretation sig univ) (β : Assignment X univ), ∀ G ∈ N, EntailsInterpret I β G

@[simp]
def SetUnsatisfiable [DecidableEq X] (N : Set (@Formula sig X)) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ), ∃ G ∈ N, ¬EntailsInterpret I β G

lemma sat_as_set_sat [inst : DecidableEq X] (F : Formula sig X) :
    @Satisfiable _ _ univ _ F → @SetSatisfiable _ _ univ _ {F} :=
  by simp only [Satisfiable, Assignment, EntailsInterpret, SetSatisfiable, Set.mem_singleton_iff,
    forall_eq, imp_self]

lemma unsat_as_set_unsat [inst : DecidableEq X]
    (F : Formula sig X) : @Unsatisfiable _ _ univ _ F → @SetUnsatisfiable _ _ univ _ {F} := by simp

theorem setEntails_iff_union_not_unsat [inst : DecidableEq X]
    (N : Set <| Formula sig X) (G : Formula sig X) :
    @SetEntails _ _ univ _ N G ↔ @SetUnsatisfiable _ _ univ _ (N ∪ {Formula.neg G}) := by
  apply Iff.intro
  · intro hNentailsG I β
    specialize hNentailsG I β
    by_cases hG : Formula.eval I β G <;> simp_all
  · intro hGornegN I β hNvalid
    cases hGornegN I β
    aesop

/-- This lemma allows us to disregard assignments when considering the entailment of closed
formulas. -/
lemma validIn_of_entails_closed {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (I : Interpretation sig univ) (F : Formula sig X) (hclosed : Formula.closed F) :
    (∃ (β : Assignment X univ), EntailsInterpret I β F) → ValidIn F I := by
  intro hβ β
  rcases hβ with ⟨γ, hγ⟩
  have heval := Formula.eval_of_closed I F hclosed β γ
  rw [EntailsInterpret, heval, ← EntailsInterpret]
  exact hγ

/- ### Lemmas Related to Entailment
In the following section, we prove several lemmas from the lecture notes that will be vital for our
soundness proof. -/

/- Composition β ∘ σ of an assignment β with a substitution σ -/
@[simp]
def Assignment.compose [DecidableEq X] (I : Interpretation sig univ) (β : Assignment X univ)
    (σ : Substitution sig X) : Assignment X univ :=
  fun x ↦ Term.eval I β (σ x)

@[simp]
def Assignment.compose_term [DecidableEq X] (I : Interpretation sig univ) (β : Assignment X univ)
    (σ : Substitution sig X) (t : Term sig X) :
    univ :=
  match t with
  | Term.var x => Term.eval I β (σ x)
  | Term.func f args => I.functions f <| args.attach.map (fun ⟨a, _⟩ =>
    Assignment.compose_term I β σ a)

lemma Assignment.compose_term_eq_eval_compose [DecidableEq X] (I : Interpretation sig univ)
    (β : Assignment X univ) (σ : Substitution sig X) (t : Term sig X) :
    Assignment.compose_term I β σ t = Term.eval I (Assignment.compose I β σ) t := by
  induction' t using Term.induction with x args ih f
  · simp_all only [compose_term, Term.eval.eq_1, compose]
  · simp_all only [compose_term, List.map_subtype, List.unattach_attach, Term.eval.eq_2]

/- I(β)(tσ) = I(β ∘ σ)(t) -/
theorem substitution_lemma [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (σ : Substitution _ _) (t : Term _ _) :
    Term.eval I β (t.substitute σ) = Term.eval I (Assignment.compose I β σ) t := by
  rw [← Assignment.compose_term_eq_eval_compose]
  induction' t using Term.induction with x args ih f
  · simp_all only [Term.substitute.eq_1, Assignment.compose_term]
  · rw [Assignment.compose_term, Term.substitute]
    simp only [List.map_subtype, List.unattach_attach, Term.eval,
      List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, List.map_map]
    have hargsarequal :
        List.map (Assignment.compose_term I β σ) args =
          List.map (Term.eval I β ∘ Term.substitute σ) args := by
      simp_all only [List.map_inj_left, Function.comp_apply, implies_true]
    rw [hargsarequal]

/- I(β)(Fσ) = A(β ∘ σ)(F) -/
theorem three_three_five [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (σ : Substitution _ _) (C : Clause _ _) :
    Formula.eval I β (C.substitute σ) = Formula.eval I (Assignment.compose I β σ) C := by
  simp_all only [Clause.substitute, eq_iff_iff]
  apply Iff.intro
  all_goals
  · intro heval
    induction' C with lit lits ih
    · simp_all only [List.map_nil, Clause.toFormula, Formula.eval]
    · induction' lit with a a
      all_goals
        rw [List.map, Literal.substitute, Clause.toFormula, Formula.eval] at *
        rcases heval with ha | hrest
        · left
          induction' a with p args
          rw [Formula.eval, Atom.substitute] at *
          simp_all only [Formula.eval, Atom.eval, List.map_map]
          have hargsarequal :
              List.map (Term.eval I β ∘ Term.substitute σ) args =
                List.map (Term.eval I (Assignment.compose I β σ)) args := by
            simp_all only [List.map_inj_left, Function.comp_apply]
            intro arg hargs
            rw [substitution_lemma]
          simp only [hargsarequal] at *
          exact ha
        · right
          exact ih hrest

-- corollary
theorem three_three_six [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (σ : Substitution _ _) (C : Clause _ _) :
    EntailsInterpret I β (C.substitute σ) ↔ EntailsInterpret I (Assignment.compose I β σ) C := by
  rw [EntailsInterpret, EntailsInterpret, ← eq_iff_iff]
  exact three_three_five I β σ C

/- A ⊨ ∀ x1, ..., xn F ↔ A ⊨ F
Since we do not demand that F is a closed formula, this statement is slightly stronger than the
one in the lecture notes. Regardless, this proof has the same structure as the one in the notes. -/
lemma three_three_seven [DecidableEq X] (n : ℕ) (F : Formula sig X) (I : Interpretation sig univ)
    (xs : List X) (huniq : xs.Nodup) (hn : xs.length = n) :
    ValidIn (F.bigForall _ _ xs) I ↔ ValidIn F I := by
  apply Iff.intro
  · intro hvalid γ
    have hlemma (as : List univ) (hlen : xs.length = as.length) :
        Formula.eval I (Assignment.bigModify γ xs as) F := by
      induction' n with n ih generalizing γ xs as F
      · aesop
      · match xs, as with
        | x :: xs, a :: as =>
          rw [Assignment.bigModify]
          have hstillvalid :
              ∀ (β : Assignment X univ), Formula.eval I β (Formula.bigForall _ _ xs F) := by
            intro β
            rw [Formula.bigForall, ValidIn] at hvalid
            specialize hvalid β
            rw [EntailsInterpret, Formula.eval] at hvalid
            specialize hvalid (β x)
            rw [Assignment.modify_rfl] at hvalid
            exact hvalid
          simp_all only [ValidIn, Assignment, EntailsInterpret, List.nodup_cons, List.length_cons,
            Nat.add_right_cancel_iff, Formula.bigForall, Formula.eval, implies_true]
        | [], [] =>
          simp_all only [ValidIn, Assignment, EntailsInterpret, List.nodup_nil, List.length_nil,
            Nat.self_eq_add_left, Nat.add_one_ne_zero]
    set as : List univ := List.map γ xs with has
    have hsubequal : γ = Assignment.bigModify γ xs as := by
      exact Assignment.substitute_equality γ xs
    rw [hsubequal]
    apply hlemma as (Eq.symm (List.length_map xs γ))
  · intro hvalid β
    induction' xs with x xs ih generalizing β n
    · simp_all only [ValidIn, Valid, Assignment, List.nodup_nil, Formula.bigForall]
    · rw [EntailsInterpret, Formula.bigForall, Formula.eval]
      intro a
      exact ih (n - 1) (List.Nodup.of_cons huniq) (Nat.eq_sub_of_add_eq hn) (β.modify x a)

/- Used in the following proof. -/
lemma valid_sub_of_valid {I : Interpretation sig univ} [DecidableEq X] (C : Clause sig X)
    (σ : Substitution sig X) :
    ValidIn (Clause.toFormula sig X C) I →
      ValidIn (Clause.toFormula sig X (Clause.substitute σ C)) I := by
  intro hvalid γ
  specialize hvalid (Assignment.compose I γ σ)
  rw [EntailsInterpret] at *
  rw [three_three_five]
  exact hvalid

/- A ⊨ ∀ x1, ..., xn F → A ⊨ ∀ y1, ..., yn F -/
lemma three_three_eight {sig : Signature} {X : Variables} [DecidableEq X] (C : Clause sig X)
    (I : Interpretation sig univ) (σ : Substitution sig X) (n m : ℕ)
    (xs ys : List X) (hxuniq : xs.Nodup) (hn : xs.length = n)
    (hyuniq : ys.Nodup) (hm : ys.length = m) :
    ValidIn (Formula.bigForall _ _ xs C.toFormula) I →
      ValidIn (Formula.bigForall _ _ ys (C.substitute σ).toFormula) I := by
  intro h
  have hl := (three_three_seven n C.toFormula I xs hxuniq hn).mp h
  apply (three_three_seven m (C.substitute σ).toFormula I ys hyuniq hm).mpr
  exact valid_sub_of_valid C σ hl
