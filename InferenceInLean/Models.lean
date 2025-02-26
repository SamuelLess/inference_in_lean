import InferenceInLean.Syntax
import InferenceInLean.Semantics

set_option autoImplicit false
--set_option diagnostics true

open Syntax
open Semantics

/- ## 3.3 Models, Validity, and Satisfiability -/

namespace Models

variable {sig : Signature} {X : Variables} {univ : Universes}

/- ### Σ-Algebra A with assignment β
> I, β ⊨ F :⇔ I(β)(F) = True
-/

@[simp]
def EntailsInterpret [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (F : Formula sig X) : Prop :=
  Formula.eval I β F

theorem not_entails_not [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (F : Formula sig X) :
    EntailsInterpret I β F → ¬EntailsInterpret I β (Formula.neg F) :=
  fun a a_1 ↦ a_1 a

/- ### Validity / Tautology
> ⊨ F :⇔ A |= F for all A ∈ Σ-Alg
-/

@[simp]
def Valid [DecidableEq X] (F : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ), Formula.eval I β F

/- ### Entailment
F ⊨ G, if for all A ∈ Σ-Alg and β ∈ X → UA, we have A, β |= F ⇒ A, β |= G
-/

@[simp]
def Entails [DecidableEq X] (F G : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ),
    EntailsInterpret I β F → EntailsInterpret I β G
infix:60 " ⊨ " => Entails

/- ### Equivalence

##### Proposition 3.3.1
> F ⊨ G if and only if F → G is valid`
-/
theorem entails_iff_imp_valid [inst : DecidableEq X]
    (F G : Formula sig X) : @Entails _ _ univ _ F G ↔ @Valid _ _ univ _ (Formula.imp F G) :=
  Eq.to_iff rfl


/- ### Sat -/
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
def SetEntails [DecidableEq X]
    (N : Set (Formula sig X)) (F : Formula sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ),
    (∀ G ∈ N, EntailsInterpret I β G) → EntailsInterpret I β F

@[simp]
def ClauseSetEntails [DecidableEq X]
    (N : Set <| Clause sig X) (C : Clause sig X) : Prop :=
  ∀ (I : Interpretation sig univ) (β : Assignment X univ),
    (∀ D ∈ N, EntailsInterpret I β D) → EntailsInterpret I β C

lemma entails_setEntails [inst : DecidableEq X]
    (F G : Formula sig X) : @Entails _ _ univ _ F G ↔ @SetEntails _ X univ _ {F} G := by simp

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

/- ### 3.3.4 Substitution Lemma -/
@[simp]
def Assignment.compose [DecidableEq X] (I : Interpretation sig univ) (β : Assignment X univ)
    (σ : Substitution sig X) (t : Term sig X) :
    univ :=
  match t with
  | Term.var x => Term.eval I β (σ x)
  | Term.func f args => I.functions f <| args.attach.map (fun ⟨a, _⟩ => Assignment.compose I β σ a)

theorem substitution_lemma [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (σ : Substitution _ _) (t : Term _ _) :
    Term.eval I β (t.substitute σ) = Assignment.compose I β σ t := by
  match t with
  | .var x => simp_all only [Term.substitute, Assignment.compose]
  | .func f args =>
    simp only [Term.substitute, List.map_subtype, List.unattach_attach, Term.eval,
      List.mem_map, forall_exists_index, and_imp, forall_apply_eq_imp_iff₂, List.map_map,
      Assignment.compose]
    have hargsareequal :
        List.map (Term.eval I β ∘ .substitute σ) args = .map (Assignment.compose I β σ) args := by
      simp only [List.map_inj_left, Function.comp_apply]
      intro t hargs
      have h := substitution_lemma I β σ t
      simp_all only
    rw [hargsareequal]

-- equivalent proof to show that the induction lemma we defined for terms actually works
theorem substitution_lemma' [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) (σ : Substitution _ _) (t : Term _ _) :
    Term.eval I β (t.substitute σ) = Assignment.compose I β σ t := by
  induction' t using Term.induction with x args ih f
  · simp only [Term.substitute, Assignment.compose]
  · rw [Assignment.compose, Term.substitute]
    simp only [List.map_subtype, List.unattach_attach, Term.eval,
      List.mem_map, forall_exists_index, and_imp,
      forall_apply_eq_imp_iff₂, List.map_map]
    have hargsarequal :
        List.map (Assignment.compose I β σ) args = .map (Term.eval I β ∘ .substitute σ) args := by
      simp_all only [List.map_inj_left, Function.comp_apply, implies_true]
    rw [hargsarequal]

/- ### Lemma 3.3.7 -/
--(hfree : ∀ x ∈ xs, x ∈ F.freeVars)
lemma three_three_seven [DecidableEq X] (n : ℕ)
    (F : Formula sig X) (xs : List X) (huniq : xs.Nodup) (hn : xs.length = n) :
    @Valid _ _ univ _ (Formula.bigForall _ _ xs F) ↔ @Valid  _ _ univ _ F := by
  apply Iff.intro
  · intro hvalid I γ
    specialize hvalid I
    have hlemma (as : List univ) (hlen : xs.length = as.length) :
        Formula.eval I (Assignment.bigModify γ xs as) F := by
      induction' n with n ih generalizing γ xs as
      · have h : xs = [] := by exact List.length_eq_zero.mp hn
        have h2 : as = [] := by rw [h] at hlen; exact List.length_eq_zero.mp (id (Eq.symm hlen))
        rw [h, h2]
        subst h2 h
        simp_all only [List.nodup_nil, List.length_nil, Assignment,
          Formula.bigForall, Assignment.bigModify]
      · match xs, as with
        | x :: xs, a :: as =>
          rw [Assignment.bigModify]
          have hstillvalid :
              ∀ (β : Assignment X univ), Formula.eval I β (Formula.bigForall _ _ xs F) := by
            intro β
            rw [Formula.bigForall] at hvalid
            specialize hvalid β
            rw [Formula.eval] at hvalid
            specialize hvalid (β x)
            rw [Assignment.modify_rfl] at hvalid
            exact hvalid
          specialize ih xs (List.Nodup.of_cons huniq) (by exact Nat.succ_inj'.mp hn)
            (γ.modify x a) hstillvalid as (Nat.succ_inj'.mp hlen)
          exact ih
        | [], [] =>
          simp_all only [List.nodup_nil, Assignment, Formula.bigForall, List.length_nil,
            Assignment.bigModify, implies_true, Nat.add_one_ne_zero]
    set as : List univ := List.map γ xs with has
    have hsubequal : γ = Assignment.bigModify γ xs as := by
      exact Assignment.substitute_equality γ xs
    rw [hsubequal]
    apply hlemma as (Eq.symm (List.length_map xs γ))
  · intro hvalid I β
    specialize hvalid I
    induction' xs with x xs ih generalizing β n
    · simp_all only [Valid, Assignment, List.nodup_nil, Formula.bigForall]
    · rw [Formula.bigForall]
      rw [Formula.eval]
      intro a
      specialize ih (n - 1) (List.Nodup.of_cons huniq) (Nat.eq_sub_of_add_eq hn) (β.modify x a)
      exact ih

/- ### Lemma 3.3.8 -/
lemma three_three_eight {sig : Signature} {X : Variables} [DecidableEq X] (n m : ℕ)
    (C : Clause sig X) (xs : List X) (hxuniq : xs.Nodup) (hn : xs.length = n)
    (σ : Substitution sig X) (ys : List X) (hyuniq : ys.Nodup) (hm : ys.length = m) :
    @Valid _ _ univ _ (Formula.bigForall _ _ xs C.toFormula) →
      @Valid _ _ univ _ (Formula.bigForall _ _ ys (C.substitute σ).toFormula) := by
  intro h
  have := (three_three_seven n C.toFormula xs hxuniq hn).mp h
  apply (three_three_seven m (C.substitute σ).toFormula ys hyuniq hm).mpr
  sorry -- use 3.3.5 (see lecture notes)
