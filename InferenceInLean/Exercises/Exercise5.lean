import InferenceInLean.F_Resolution
import Mathlib.Data.Finset.Defs
import Mathlib.Data.Set.Card
import Mathlib.SetTheory.Cardinal.Finite

set_option autoImplicit false

open Syntax
open Semantics
open Models
open Unification
open Inferences

variable {sig : Signature} {X : Variables} {univ : Universes}

/- ## Exercise 5 -/

namespace Exercise5

/- ### Exercise 5-1 -/

namespace Task1

/- Claude Sonnet 3.7 (free version) was involved in some of these solutions. -/

inductive funs where | b | f deriving BEq
inductive preds where | P deriving BEq

def sig5_1 : Signature := ⟨funs, preds⟩

def b : Term sig5_1 String := .func .b []
def f : List (Term sig5_1 String) -> Term sig5_1 String := .func .f
def P : List (Term sig5_1 String) -> Formula sig5_1 String := fun args =>.atom <| .pred .P args

/- Force the interpretation of P to be false for every list of arguments with the wrong arity. -/
def ArityP (ps : preds -> List (GroundTerm sig5_1) -> Prop) : Prop :=
  ∀ (args : List (GroundTerm sig5_1)), (args.length ≠ 1) → ¬(ps .P args)

-- (1) There is a Σ-model A of P (b) ∧ ¬P (f (b)) such that UA = {7, 8, 9}.
def F₁ : Formula sig5_1 String := (P [b]).and (.neg (P [f [b]]))
theorem task5_1_1 : ∃ (I : Interpretation sig5_1 (Fin 3)), ∀ β : Assignment String (Fin 3),
    EntailsInterpret I β F₁ := by
  -- Define the interpretation I for universe {0, 1, 2} (representing {7, 8, 9})
  let I : Interpretation sig5_1 (Fin 3) := ⟨
    -- Function interpretations
    fun g args => match g with
      | .b => 0  -- Interpret b as 0 (representing 7)
      | .f => match args with
              | [x] => 1  -- Interpret f(x) as 1 (representing 8) for any x
              | _ => 0,   -- Default case
    -- Predicate interpretations
    fun p args => match p with
      | .P => match args with
              | [x] => x = 0  -- P is true only for 0 (representing 7)
              | _ => false⟩   -- Default case
  use I
  intro β
  simp [F₁, EntailsInterpret, I, P, b, f]

-- (2) There is no Σ-model A of P (b) ∧ ¬P (f (f (b))) such that fA (a) = a for every a ∈ UA.
def F₂ : Formula sig5_1 String := (P [b]).and (.neg (P [f [f [b]]]))
theorem task5_1_2 : ¬∃ (univ : Universes) (I : Interpretation sig5_1 univ),
    ∀ β : Assignment String univ, EntailsInterpret I β F₂ ∧
    (∀ a, (I.functions .f) [a] = a):= by
  -- Get the universe and interpretation from the hypothesis
  intro ⟨univ, I, hI⟩
  have h := hI (fun _ => I.functions .b [])
  obtain ⟨h_entails, h_identity⟩ := h
  obtain ⟨h_P_b, h_not_P_ffb⟩ := h_entails
  let bval := I.functions .b []
  have h_fb : I.functions .f [bval] = bval := h_identity bval
  have h_ffb : I.functions .f [I.functions .f [bval]] = bval := by
    rw [h_fb]
    exact h_fb
  have h_P_bval : I.predicates .P [bval] := by
    simp [P,b] at h_P_b
    exact h_P_b
  have h_not_P_ffbval : ¬I.predicates .P [bval] := by
    simp [Formula.eval, P, f, b] at h_not_P_ffb
    rw [h_ffb] at h_not_P_ffb
    exact h_not_P_ffb
  contradiction

-- (3) P(b) ∧ ¬P(f (b)) has a Herbrand model.
theorem task5_1_3 : ∃ preds, ∀ β, EntailsInterpret (HerbrandInterpretation sig5_1 preds) β F₁ := by
  -- First, let's define our Herbrand interpretation
  -- We need to define how predicates behave on ground terms
  let preds : sig5_1.preds → List (GroundTerm sig5_1) → Prop := fun p args =>
    match p, args with
    | .P, [.func .b []] => True
    | .P, [.func .f [.func .b []]] => False
    | .P, _ => False
  use preds
  intro β
  simp [F₁, EntailsInterpret]
  apply And.intro
  · simp [Atom.eval, Term.eval, preds, P, b]
  · simp [Atom.eval, preds, P, f, b]

-- (4) P(b) ∧ ∀x ¬P(x) has no Herbrand model.
def F₄ : Formula sig5_1 String := .and (P [b]) (.all "x" (.neg (P [.var "x"])))
theorem task5_1_4 : ¬∃ preds, ∀ β, EntailsInterpret (HerbrandInterpretation sig5_1 preds) β F₄ := by
  let b' : GroundTerm sig5_1 := Term.func .b []
  intro h
  rcases h with ⟨preds, h⟩
  let β₀ : Assignment String (GroundTerm sig5_1) := fun _ => b'
  have h₀ := h β₀
  have hPb : preds .P [b'] := by
    simp [F₄, P, b] at h₀
    exact h₀.1
  obtain ⟨_, h_forall⟩ := h₀
  let β₁ : Assignment String (GroundTerm sig5_1) := β₀.modify "x" b'
  have hNotPb : ¬preds .P [b'] := by
    simp [Formula.eval, HerbrandInterpretation] at h_forall
    specialize h_forall b'
    simp [P] at h_forall
    exact h_forall
  contradiction

-- (5) ∀x P (f (x)) does not have a Herbrand model with a two-element universe.
def F₅ : Formula sig5_1 String := .all "x" (P [f [.var "x"]])
theorem task5_1_5  (S : Set <| GroundTerm sig5_1) (hall : ∀ t : GroundTerm sig5_1, t ∈ S) :
    Set.encard S ≠ 2 := by
  let t₀ : GroundTerm sig5_1 := .func .b []
  let t₁ : GroundTerm sig5_1 := .func .f [t₀]
  let t₂ : GroundTerm sig5_1 := .func .f [t₁]
  let t₃ : GroundTerm sig5_1 := .func .f [t₂]
  let S' : Set (GroundTerm sig5_1) := {t₀, t₁, t₂}
  have ht₀ := hall t₀
  have ht₁ := hall t₁
  have ht₂ := hall t₂
  have hsub : S' ⊆ S := by
    simp [Set.subset_def, S']
    exact ⟨ht₀, ht₁, ht₂⟩
  have hS'finite : S'.Finite := by aesop
  have hS'ncard3 : S'.ncard = 3 := by aesop
  have hS'encard3 : S'.encard = 3 := by
    have := hS'finite.cast_ncard_eq
    aesop
  have hle := Set.encard_le_encard hsub
  intro hSncard2
  rw [hS'encard3, hSncard2] at hle
  contradiction

-- (6) ∀x P(x) has exactly one Herbrand model.
def F₆ : Formula sig5_1 String := .all "x" (P [.var "x"])
theorem task5_1_6 : ∃! ps,
    (ArityP ps ∧ ∀ β, EntailsInterpret (HerbrandInterpretation sig5_1 ps) β F₆) := by
  use fun _ args => args.length = 1
  apply And.intro
  · constructor
    · simp [ArityP]
    · intro β
      simp [F₆, P]
  · intro preds' ⟨h_arity, h_entails⟩
    ext p args
    cases p
    -- Let's prove that P must be true for all args for preds'
    have h : ∀ (t : GroundTerm sig5_1), preds' .P [t] := by
      intro t
      -- Create an assignment that maps x to t
      let β : Assignment String (GroundTerm sig5_1) := fun v => Term.func .b []
      -- Use the entailment hypothesis
      have h_entails_β := h_entails β
      -- Extract the universal quantifier's meaning
      simp [F₆, P] at h_entails_β
      -- Show that P holds for t
      specialize h_entails_β t
      exact h_entails_β
    simp_all only [EntailsInterpret]
    cases args with
    | nil =>
      simp_all only [ArityP, ne_eq, List.length_nil, zero_ne_one, not_false_eq_true]
    | cons head tail =>
      aesop

-- (7) ∀x P(f(x)) entails ∀x P(f(f(x))).
def F₇ : Formula sig5_1 String := .all "x" (P [f [.var "x"]])
def F₇' : Formula sig5_1 String := .all "y" (P [f [f [.var "y"]]])
theorem task5_1_7 : @Entails _ _ univ _ F₇ F₇' := by simp_all [F₇, F₇', f, P]


end Task1

end Exercise5
