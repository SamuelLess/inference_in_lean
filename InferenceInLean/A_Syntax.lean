import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Range

set_option autoImplicit false

/-! ## 3.1 Syntax
In this section, we define the basic syntactic notions for first-order logic. This includes terms,
atoms, formulas, Literals, and clauses. For each of these constructs, we also define its set of
free variables, and how substitutions act on them. -/

namespace Syntax

/- ### Basic Definitions -/

structure Signature where
  /-- The type of the syntactic function symbols -/
  funs : Type
  /-- The type of the syntactic predicate symbols -/
  preds : Type

def Variables := Type

variable (sig : Signature) (X : Variables)

/- Terms are either variables x, or functions f(t1, ..., tn) with subterms t1, ..., tn; this allows
us to define constants as functions f() of arity zero (i.e., args = []). -/
inductive Term where
  | var (x : X)
  | func (f : sig.funs) (args: List Term)

abbrev GroundTerm (sig : Signature) := Term sig Empty

/- Term is a nested inductive type, so induction does not work out of the box. Rather than proving
statements about terms via recursion, we define our own induction scheme. -/
lemma Term.induction {P : (Term sig X) → Prop}
    (base : ∀ x : X, P (var x)) (step : ∀ (args : List (Term sig X)),
      (ih : ∀ term ∈ args, P term) → ∀ (f : sig.funs), P (func f args)) :
    ∀ (t : Term sig X), P t := by
  intro t
  match t with
  | var x => simp_all only
  | func f args =>
    apply step
    intro term harg
    apply Term.induction
    · exact base
    · intro args' ih f'
      apply step
      intro term' harg'
      exact ih term' harg'

mutual
  def eqTerm [instX : BEq X] [instF : BEq sig.funs] :
      Term sig X → Term sig X → Bool
    | Term.var x, Term.var y => x == y
    | Term.func f fargs, Term.func g gargs => f == g && eqArgs fargs gargs
    | _, _ => false
  def eqArgs [instX : BEq X] [instF : BEq sig.funs] :
      List (Term sig X) → List (Term sig X) → Bool
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | x :: xs, y :: ys => eqTerm x y && eqArgs xs ys
end

instance [instX : BEq X] [instF : BEq sig.funs] : BEq (Term sig X) := ⟨eqTerm sig X⟩

/- Defining free variables for terms is straight-forward: Every variable occurring in a term is
free per default. The free variables of a function f(t1, ..., tn) are the union of the free
variables of the subterms t1, ..., tn. -/
@[simp]
def Term.freeVars : Term sig X -> Set X
  | .var x => {x}
  | .func _ [] => ∅
  | .func f (a :: args) => Term.freeVars a ∪ Term.freeVars (Term.func f args)

lemma Term.arg_subset_of_freeVars {sig : Signature} {X : Variables}
    [_inst : DecidableEq X] (args : List (Term sig X)) (f : sig.funs) :
    ∀ (arg : Term sig X) (_harg : arg ∈ args),
    Term.freeVars sig X arg ⊆ Term.freeVars sig X (Term.func f args) := by
  intro arg harg
  induction' args with arg' args ih
  · simp_all only [List.not_mem_nil]
  · simp only [List.mem_cons] at harg
    rcases harg with harg | harg
    · subst harg
      simp_all only [Term.freeVars.eq_3, Set.subset_union_left]
    · specialize ih harg
      rw [Term.freeVars]
      exact Set.subset_union_of_subset_right ih (Term.freeVars sig X arg')

/- Atoms are of the form P(t1, ..., tn) with terms t1, ..., tn. -/
inductive Atom where
  | pred (p : sig.preds) (args : List (Term sig X))

@[simp]
def Atom.freeVars {sig : Signature} {X : Variables} : Atom sig X -> Set X
  | .pred _ [] => ∅
  | .pred P (a :: args) => a.freeVars ∪ (Atom.pred P args).freeVars

inductive Literal where
  /-- a -/
  | pos (a : Atom sig X)
  /-- ¬a -/
  | neg (a : Atom sig X)

@[simp]
def Literal.comp : Literal sig X -> Literal sig X
  | .pos a => .neg a
  | .neg a => .pos a

@[simp]
def Clause := List (Literal sig X)

instance : Membership (Literal sig X) (Clause sig X) :=
  List.instMembership

instance : Append (Clause sig X) :=
  List.instAppend

instance : HAppend (Clause sig X) (Clause sig X) (Clause sig X) :=
  instHAppendOfAppend

/- This follows the definition from the lecture notes, though ¬, ∧, ∀ would suffice. -/
inductive Formula where
  | falsum
  | verum
  | atom (a : Atom sig X)
  | neg (f : Formula)
  | and (f g : Formula)
  | or (f g : Formula)
  | imp (f g : Formula)
  | iff (f g : Formula)
  | all (x : X) (f : Formula)
  | ex (x : X) (f : Formula)

/-- ⊤ and ⊥ have no free variables. The free variables of ¬F are the free variables of F. For
F * G, with * ⊆ {∧, ∨, →, ↔}, the free formulas are the union of the free formulas of F and the
free formulas of G.
Quantifiers can bind variables: The free variables of ∀ x, F and ∃ x, F are the free variables of
F with x removed.  -/
@[simp]
def Formula.freeVars {sig : Signature} {X : Variables} : Formula sig X -> Set X
  | Formula.falsum => ∅
  | Formula.verum => ∅
  | Formula.atom a => Atom.freeVars a
  | Formula.neg f => Formula.freeVars f
  | Formula.and f g => Formula.freeVars f ∪ Formula.freeVars g
  | Formula.or f g => Formula.freeVars f ∪ Formula.freeVars g
  | Formula.imp f g => Formula.freeVars f ∪ Formula.freeVars g
  | Formula.iff f g => Formula.freeVars f ∪ Formula.freeVars g
  | Formula.all x f => Formula.freeVars f \ {x}
  | Formula.ex x f => Formula.freeVars f \ {x}

/-- A clause [a1, ..., an] can be converted into a formula a1 ∨ ... ∨ an -/
@[simp]
def Clause.toFormula : Clause sig X -> Formula sig X
  | [] => Formula.falsum
  | .pos l :: ls => (Formula.atom l).or (Clause.toFormula ls)
  | .neg l :: ls => Formula.or (Formula.atom l).neg (Clause.toFormula ls)

instance : Coe (Clause sig X) (Formula sig X) :=
  ⟨Clause.toFormula sig X⟩

instance : Coe (Set <| Clause sig X) (Set <| Formula sig X) :=
  ⟨fun N => {↑C | C ∈ N}⟩

@[simp]
def Formula.closed {sig : Signature} {X : Variables} (F : Formula sig X) : Prop :=
  Formula.freeVars F = ∅

/- ### bigForall -/

/-- Creates formula ∀ x1 ... xn, F. -/
@[simp]
def Formula.bigForall [DecidableEq X]
    (xs : List X) (F : Formula sig X) : Formula sig X :=
  match xs with
  | [] => F
  | x :: xs => .all x (F.bigForall xs)

/-- The free formulas of ∀ x1 ... xn, F are a subset of the free formulas of F. -/
@[simp]
lemma Formula.bigForall_freeVars_subset [DecidableEq X] (xs : List X) (F : Formula sig X) :
    (F.bigForall sig X xs).freeVars ⊆ F.freeVars := by
  induction' xs with x xs ih
  · simp_all only [bigForall, subset_refl]
  · simp_all only [bigForall, freeVars, Set.diff_singleton_subset_iff]
    intro x' hx'
    simp_all only [Set.mem_insert_iff]
    apply Or.inr
    apply ih
    simp_all only

/-- The free variables of ∀ x, ∀ x1 ... xn, F are the free variables of ∀ x1 ... xn, ∀ x, F. -/
lemma Formula.bigForall_all [DecidableEq X] (xs : List X) (F : Formula sig X) (x : X) :
    (bigForall sig X xs (all x F)).freeVars = (all x (bigForall sig X xs F)).freeVars := by
  simp_all only [freeVars]
  induction' xs with y xs ih
  · simp_all only [List.not_mem_nil, or_false, Set.setOf_eq_eq_singleton,
      Set.subset_singleton_iff, bigForall, freeVars]
  · simp_all only [List.mem_cons, bigForall, freeVars]
    ext x_1 : 1
    simp_all only [Set.mem_diff, Set.mem_singleton_iff]
    apply Iff.intro
    · intro a
      simp_all only [not_false_eq_true, and_self]
    · intro a
      simp_all only [not_false_eq_true, and_self]

/-- If the free variables of F are contained in [x1, ..., xn], then the formula ∀ x1 ... xn, F
is closed. -/
@[simp]
lemma Formula.bigForall_subset_freeVars [DecidableEq X] (xs : List X) (F : Formula sig X) :
    F.freeVars ⊆ xs.toFinset → (F.bigForall sig X xs).closed := by
  intro hmem
  simp_all only [List.coe_toFinset, closed]
  induction' xs with x xs ih generalizing F
  · simp_all only [List.not_mem_nil, Set.setOf_false, Set.subset_empty_iff, bigForall]
  · rw [bigForall, freeVars]
    simp_all only [List.mem_cons, bigForall, freeVars]
    specialize ih (.all x F)
      (by simp_all only [freeVars, Set.diff_singleton_subset_iff]; exact hmem)
    have hsymm := bigForall_all sig X xs F x
    simp_all only [freeVars]

/- ### Lemmas related to free variables -/

/- A term without free variables cannot be a variable. -/
@[simp]
lemma Term.eval_without_free_not_term {sig : Signature} {X : Variables} [DecidableEq X]
    (t : Term sig X) : t.freeVars = {} → ¬∃ (x : X), t = Term.var x := by aesop

lemma Set.singleton_of_union_empty {α : Type} {x : α} {A B : Set α}
    (h : ¬A = {x}) (hsingleton : A ∪ B = {x}) : A = ∅ := by
  have sub : A ⊆ {x} := by
    rw [← hsingleton]
    exact Set.subset_union_left
  have : A = ∅ ∨ A = {x} := by
    exact Set.subset_singleton_iff_eq.mp sub
  simp_all only [Set.subset_singleton_iff, or_false]

/- All subterms t1, ..., tn of a closed term f(t1, ..., tn) are closed as well -/
@[simp]
lemma Term.subterms_closed {sig : Signature} {X : Variables}
    [DecidableEq X] (t : Term sig X) (_x : X) :
    ∀ (f : sig.funs) (args : List (Term sig X)), t = Term.func f args →
    t.freeVars = {} →
    ∀ (arg : Term sig X) (_harg : arg ∈ args), arg.freeVars = {} := by
  intro f args ht hclosed arg harg
  subst ht
  induction' args with arg' args' ih generalizing arg
  · simp_all only [List.not_mem_nil]
  · aesop

@[simp]
lemma Term.one_freeVar_of_subterms {sig : Signature} {X : Variables} [DecidableEq X]
    {t : Term sig X} {x : X} :
    ∀ (f : sig.funs) (args : List (Term sig X)), t = Term.func f args →
      t.freeVars = {x} → ∀ (arg : Term sig X) (_harg : arg ∈ args),
        arg.freeVars = {x} ∨ arg.freeVars = {} := by
  intro f args ht honefree arg harg
  induction' args with arg' args' ih generalizing arg t
  · simp_all only [Term.freeVars.eq_2, Term.func.injEq, or_self, List.not_mem_nil]
  · simp_all only [Term.freeVars.eq_3, Term.func.injEq, List.cons_ne_self, and_false,
    IsEmpty.forall_iff, implies_true, List.mem_cons]
    by_cases h : Term.freeVars sig X arg = {x}
    · left
      exact h
    · rcases harg with h₁ | h₂
      · subst h₁
        subst ht
        simp_all only [false_or]
        clear ih
        generalize Term.freeVars sig X arg = A, Term.freeVars sig X (Term.func f args') = B at *
        exact Set.singleton_of_union_empty h honefree
      · subst ht
        simp_all only [false_or]
        specialize @ih (Term.func f args') rfl
        by_cases h' : Term.freeVars sig X (Term.func f args') = {x}
        · specialize ih h' arg h₂
          simp_all only [Set.union_singleton, false_or]
        · simp_all only [IsEmpty.forall_iff]
          generalize hA : Term.freeVars sig X (Term.func f args') = A,
            hB : Term.freeVars sig X arg' = B at *
          have hempty : A = {} := by
            rw [Set.union_comm] at honefree
            exact Set.singleton_of_union_empty h' honefree
          clear honefree
          induction' args' with arg' args ih
          · simp_all only [List.not_mem_nil]
          · aesop

/- Generates the free variables of a term as a list, rather than as a set. -/
@[simp]
def Term.freeVarsList [DecidableEq X] : Term sig X -> List X
  | Term.var x => [x]
  | Term.func _ [] => []
  | Term.func f (a :: args) => List.dedup
    ((Term.freeVarsList a).append (Term.freeVarsList (Term.func f args)))

@[simp]
lemma Term.freeVars_sub_freeVarsList [DecidableEq X] (t : Term sig X) :
    t.freeVars ⊆ (t.freeVarsList).toFinset := by
  induction' t using Term.induction with x args ih f
  · aesop
  · induction args with
    | nil => aesop
    | cons head tail ih' =>
      simp
      constructor
      · specialize ih head (by simp)
        generalize freeVarsList sig X head = Fl at *
        generalize freeVars sig X head = Fs at *
        intro x hxinFs
        simp only [Set.mem_setOf_eq]
        left
        exact List.mem_dedup.mp (ih hxinFs)
      · simp_all only [List.coe_toFinset]
        intro x hxinfree
        aesop

@[simp]
lemma Term.freeVarsList_sub_freeVars [DecidableEq X] (t : Term sig X) :
    ↑(t.freeVarsList).toFinset ⊆ t.freeVars := by
  induction' t using Term.induction with x args ih f
  · simp_all only [freeVarsList, List.toFinset_cons, List.toFinset_nil, insert_emptyc_eq,
      Finset.coe_singleton, freeVars, subset_refl]
  · induction' args with arg args ih' generalizing f
    · simp_all only [List.not_mem_nil, List.coe_toFinset, IsEmpty.forall_iff, implies_true,
        freeVarsList, List.toFinset_nil, Finset.coe_empty, freeVars, subset_refl]
    · simp_all only [List.coe_toFinset, List.mem_cons, forall_eq_or_imp, freeVarsList,
        List.append_eq, List.mem_dedup,
      List.mem_append, freeVars, implies_true, forall_const]
      obtain ⟨ihleft, ihright⟩ := ih
      intro x hx
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      cases hx with
      | inl h =>
        apply Or.inl
        apply ihleft
        simp_all only [Set.mem_setOf_eq]
      | inr h_1 =>
        right
        clear ihleft
        induction' args with arg' args' ih'
        · simp_all only [List.not_mem_nil, IsEmpty.forall_iff, implies_true, freeVarsList]
        · simp_all only [List.mem_cons, or_true, implies_true, forall_const, forall_eq_or_imp,
            freeVarsList, List.append_eq, List.mem_dedup, List.mem_append, freeVars, Set.mem_union]
          obtain ⟨left, right⟩ := ihright
          cases h_1 with
          | inl h =>
            apply Or.inl
            apply left
            simp_all only [Set.mem_setOf_eq]
          | inr h_2 => simp_all only [forall_const, or_true]

/- Generates the free variables of an atom as a list, rather than as a set. -/
@[simp]
def Atom.freeVarsList [DecidableEq X] : Atom sig X -> List X
  | .pred _ [] => []
  | .pred P (t :: ts) => List.dedup ((t.freeVarsList).append (Atom.pred P ts).freeVarsList)

lemma Atom.freeVars_sub_freeVarsList [DecidableEq X] (a : Atom sig X) :
    a.freeVars ⊆ (a.freeVarsList).toFinset := by
  simp_all only [List.coe_toFinset]
  induction a with
  | pred p args =>
    induction args with
    | nil => aesop
    | cons head tail ih =>
      simp only [freeVars, Set.union_subset_iff]
      unfold freeVarsList
      constructor <;> intro x hxinfree
      · have hfree_subset := Term.freeVars_sub_freeVarsList sig X head
        simp_all only [List.coe_toFinset, List.append_eq, List.mem_dedup, List.mem_append,
          Set.mem_setOf_eq]
        apply Or.inl
        apply hfree_subset
        simp_all only
      · simp_all only [List.coe_toFinset, List.append_eq, List.mem_dedup, List.mem_append,
          Set.mem_setOf_eq]
        apply Or.inr
        apply ih
        exact hxinfree

lemma Atom.freeVarsList_sub_freeVars[DecidableEq X] (a : Atom sig X) :
    ↑(a.freeVarsList).toFinset ⊆ a.freeVars := by
  induction' a with p args
  intro x hmem
  simp_all only [List.coe_toFinset, Set.mem_setOf_eq]
  induction' args with arg args ih
  · simp_all only [freeVarsList, List.not_mem_nil]
  · simp_all only [freeVarsList, List.append_eq, List.mem_dedup, List.mem_append, freeVars,
      Set.mem_union]
    cases hmem with
    | inl h =>
      left
      have l := Term.freeVarsList_sub_freeVars sig X arg
      simp_all only [List.coe_toFinset]
      apply l
      simp_all only [Set.mem_setOf_eq]
    | inr h_1 => simp_all only [forall_const, or_true]

/- Generates the free variables of a clause as a list, rather than as a set. -/
@[simp]
def Clause.freeVarsList [DecidableEq X] : Clause sig X -> List X
  | [] => []
  | (.pos l) :: ls => List.dedup (l.freeVarsList ++ freeVarsList ls)
  | (.neg l) :: ls => List.dedup (l.freeVarsList ++ freeVarsList ls)

lemma Clause.freeVars_sub_freeVarsList [DecidableEq X] (C : Clause sig X) :
    (C.toFormula).freeVars ⊆ ↑(C.freeVarsList).toFinset := by
  induction' C with lit lits ih
  · simp_all only [freeVarsList, List.toFinset_nil, Finset.coe_empty, toFormula, Formula.freeVars,
      subset_refl]
  · simp_all only [List.coe_toFinset]
    match lit with
    | .pos a =>
      simp_all only [freeVarsList, List.mem_dedup, List.mem_append, toFormula, Formula.freeVars]
      intro x
      intro a_1
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      cases a_1 with
      | inl h =>
        left
        have hfree := Atom.freeVars_sub_freeVarsList sig X a
        simp_all only [List.coe_toFinset]
        apply hfree
        simp_all only [Set.mem_setOf_eq]
      | inr h_1 =>
        apply Or.inr
        apply ih
        simp_all only [Set.mem_setOf_eq]
    | .neg a =>
      simp_all only [freeVarsList, List.mem_dedup, List.mem_append, toFormula, Formula.freeVars]
      intro x
      intro a_1
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      cases a_1 with
      | inl h =>
        left
        have hfree := Atom.freeVars_sub_freeVarsList sig X a
        simp_all only [List.coe_toFinset]
        apply hfree
        simp_all only [Set.mem_setOf_eq]
      | inr h_1 =>
        apply Or.inr
        apply ih
        simp_all only [Set.mem_setOf_eq]

lemma Clause.freeVarsList_sub_freeVars [DecidableEq X] (C : Clause sig X) :
    ↑(C.freeVarsList).toFinset ⊆ (C.toFormula).freeVars := by
  induction' C with lit lits ih
  · simp_all only [freeVarsList, List.toFinset_nil, Finset.coe_empty, toFormula, Formula.freeVars,
      subset_refl]
  · simp_all only [List.coe_toFinset]
    match lit with
    | .pos a =>
      simp_all only [freeVarsList, List.mem_dedup, List.mem_append, toFormula, Formula.freeVars]
      intro x
      intro a_1
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      cases a_1 with
      | inl h =>
        left
        have hfree := Atom.freeVarsList_sub_freeVars sig X a
        simp_all only [List.coe_toFinset]
        apply hfree
        simp_all only [Set.mem_setOf_eq]
      | inr h_1 =>
        apply Or.inr
        apply ih
        simp_all only [Set.mem_setOf_eq]
    | .neg a =>
      simp_all only [freeVarsList, List.mem_dedup, List.mem_append, toFormula, Formula.freeVars]
      intro x
      intro a_1
      simp_all only [Set.mem_setOf_eq, Set.mem_union]
      cases a_1 with
      | inl h =>
        left
        have hfree := Atom.freeVarsList_sub_freeVars sig X a
        simp_all only [List.coe_toFinset]
        apply hfree
        simp_all only [Set.mem_setOf_eq]
      | inr h_1 =>
        apply Or.inr
        apply ih
        simp_all only [Set.mem_setOf_eq]

@[simp]
lemma nodup_clauseFreeVarsList [DecidableEq X] (C : Clause sig X) :
    List.Nodup (C.freeVarsList) := by
  unfold Clause.freeVarsList
  simp_all only [Clause]
  split <;> simp_all only [List.nodup_nil, List.nodup_dedup]

/-- Converts a clause to a closed formula by quantifying it with each of its free variables.  -/
@[simp]
def Clause.toClosedFormula [DecidableEq X] (C : Clause sig X) : Formula sig X :=
  Formula.bigForall sig X (C.freeVarsList) C

lemma Clause.closedEmpty_closed [DecidableEq X] :
    Formula.closed (Clause.toClosedFormula sig X []) := by aesop

lemma Clause.consClosed [DecidableEq X] (L : Literal sig X) (C : Clause sig X) :
    (Clause.toClosedFormula sig X C).closed → (Clause.toClosedFormula sig X (L :: C)).closed := by
  intro h
  simp_all only [toClosedFormula]
  induction' L with a a
  simp_all only [freeVarsList, List.append_nil, toFormula]
  have horsubset := Formula.bigForall_subset_freeVars sig X
    (Atom.freeVarsList sig X a ++ freeVarsList sig X C).dedup
    ((Formula.atom a).or (toFormula sig X C))
  swap
  simp_all only [freeVarsList, List.append_nil, toFormula]
  have horsubset := Formula.bigForall_subset_freeVars sig X
    (Atom.freeVarsList sig X a ++ freeVarsList sig X C).dedup
    ((Formula.atom a).neg.or (toFormula sig X C))
  all_goals
  have hatomsubset := Atom.freeVars_sub_freeVarsList sig X a
  have hclausesubset := Clause.freeVars_sub_freeVarsList sig X C
  simp_all only [Formula.closed, List.coe_toFinset, List.mem_dedup, List.mem_append,
    Formula.freeVars]
  apply horsubset
  intro x
  aesop

theorem Clause.closedClause_closed [DecidableEq X] (C : Clause sig X) :
    Formula.closed C.toClosedFormula := by
  induction C with
  | nil => aesop
  | cons head tail ih =>
    simp_all
    exact Clause.consClosed sig X head tail ih

/- ### Substitutions -/

/-- A substitution σ replaces each variable with another term. We do not strictly require the
substitution to have a finite domain, as that constraint does not change the outcome of our
proofs. -/
@[simp]
def Substitution := X -> Term sig X

/- Modifies a substitution σ by indicating that one of the variables x should be replaced with
another term a instead. In the lecture notes, this is written as σ[x ↦ a]. -/
@[simp]
def Substitution.modify {sig : Signature} {X : Variables} [DecidableEq X]
    (σ : Substitution sig X) (x : X) (a : Term sig X) : Substitution sig X :=
  fun y => if y = x then a else σ y

/- The following definitions describe how substitutions work on terms, atoms, literals, and clauses
respectively: For the base case, i.e. a variable x, we just apply the substitution to the variable.
In all other cases, we apply the substitution inductively. -/
@[simp]
def Term.substitute {sig : Signature} {X : Variables} (σ : Substitution sig X) :
    Term sig X -> Term sig X
  | Term.var x => σ x
  | Term.func f args => Term.func f <| args.attach.map (fun ⟨a, _⟩ => a.substitute σ)

@[simp]
def Atom.substitute {sig : Signature} {X : Variables} (σ : Substitution sig X) :
    Atom sig X -> Atom sig X
  | Atom.pred p ts => Atom.pred p (ts.map (Term.substitute σ))

@[simp]
def Literal.substitute {sig : Signature} {X : Variables} (σ : Substitution sig X) :
    Literal sig X -> Literal sig X
  | Literal.pos a => Literal.pos (a.substitute σ)
  | Literal.neg a => Literal.neg (a.substitute σ)

@[simp]
def Clause.substitute {sig : Signature} {X : Variables}
    (σ : Substitution sig X) (C : Clause sig X) : Clause sig X :=
  C.map (Literal.substitute σ)

@[simp]
def Substitution.compose {sig : Signature} {X : Variables} (σ τ: Substitution sig X) :
    Substitution sig X :=
  fun x => (τ x).substitute σ
infix:90 " ∘ " => Substitution.compose

@[simp]
def Substitution.domain {sig : Signature} {X : Variables} (σ : Substitution sig X) : Set X :=
  {x | σ x ≠ Term.var x}

@[simp]
def Substitution.codomain {sig : Signature} {X : Variables} (σ : Substitution sig X) : Set X :=
  {x | ∃ y ∈ σ.domain, x ∈ (σ y).freeVars}

@[simp]
def MoreGeneral {sig : Signature} {X : Variables} [BEq X] (σ τ : Substitution sig X) : Prop :=
  ∃ ρ : Substitution sig X, ρ ∘ σ = τ
infix:50 " ≤ " => MoreGeneral

def example_subst : Substitution (Signature.mk String String) String :=
  fun x => if x == "z" then Term.func "f" [Term.var "y"] else Term.var x

def example_subst' : Substitution (Signature.mk String String) String :=
  fun x => if x == "z" then Term.func "f" [Term.var "z"] else
    if x == "y" then Term.var "z" else Term.var x

theorem example_more_general : example_subst ≤ example_subst' := by
  use fun x => if x == "y" then Term.var "z" else Term.var x
  funext x
  simp [example_subst, example_subst']
  by_cases hx : x = "z" <;> by_cases hy : x = "y" <;> simp [hx, hy]

@[simp]
def Idempotent {sig : Signature} {X : Variables} [BEq X] (σ : Substitution sig X) : Prop :=
  σ ∘ σ = σ

@[simp]
lemma Substitution.id_of_domain_empty {sig : Signature} {X : Variables} [BEq X]
    (σ : Substitution sig X) (t : Term sig X) :
    σ.domain = ∅ → t.substitute σ = t := by
  intro hdomempty
  induction' t using Term.induction with x args ih f
  · have hxnindom : x ∉ σ.domain := by
      simp_all only [domain, ne_eq, Set.mem_empty_iff_false, not_false_eq_true]
    simp_all
    by_cases h : σ x = Term.var x
    · exact h
    · exact False.elim (Set.eq_empty_iff_forall_not_mem.mp hdomempty x h)
  · induction args with
    | nil => simp only [Term.substitute, List.attach_nil, List.map_nil]
    | cons head tail ihargs => aesop

@[simp]
lemma Substitution.id_of_freeVars_empty {sig : Signature} {X : Variables} [BEq X]
    (σ : Substitution sig X) (t : Term sig X) :
    t.freeVars = ∅ → t.substitute σ = t := by
  intro hfreeempty
  induction' t using Term.induction with x args ih f
  · simp_all only [Term.freeVars, Set.singleton_ne_empty]
  · induction args <;> simp_all

@[simp]
lemma Substitution.id_of_free_not_in_domain {sig : Signature} {X : Variables} [BEq X]
    (σ : Substitution sig X) (t : Term sig X) :
    (∀ x ∈ t.freeVars, x ∉ σ.domain) → t.substitute σ = t := by
  intro hfreenoindom
  simp_all only [Substitution.domain, ne_eq, Set.mem_setOf_eq, not_not]
  induction' t using Term.induction with x args ih f
  · simp_all only [Term.freeVars, Set.mem_singleton_iff, Term.substitute]
  · induction args <;> simp_all

@[simp]
lemma Substitution.ne_subst_of_mem_dom_free {sig : Signature} {X : Variables} [BEq X] [BEq sig.funs]
    (σ : Substitution sig X) (t : Term sig X) :
    (∃ x ∈ σ.domain, x ∈ t.freeVars) → t ≠ t.substitute σ := by
  intro ⟨x,⟨hxindom, hxinfree⟩⟩
  simp_all
  by_contra teqtsub
  induction' t using Term.induction with x' args ih f
  · rw [Term.substitute.eq_def] at teqtsub
    simp_all
    rw [symm teqtsub] at hxinfree
    simp only [Term.freeVars] at hxinfree
    subst hxinfree
    simp_all only [not_true_eq_false]
  · induction args with
    | nil =>
      simp [Term.freeVars] at hxinfree
    | cons head tail ihargs =>
      simp only [List.mem_cons, forall_eq_or_imp] at ih
      obtain ⟨hxinheadimp, hforallintail⟩ := ih
      have hxintailimp := ihargs hforallintail
      simp only [Term.substitute, List.attach_cons, List.map_cons, List.map_map,
        Function.comp_apply, List.map_subtype, List.unattach_attach, Term.func.injEq,
        List.cons.injEq, true_and] at teqtsub
      obtain ⟨hheqhsub, hteqsubt⟩ := teqtsub
      by_cases hxinhead : x ∈ head.freeVars
      · exact hxinheadimp hxinhead hheqhsub
      · simp [List.mem_cons, List.cons_inj_right] at hxinfree
        have hxintail : x ∈ (Term.func f tail).freeVars := or_iff_not_imp_left.mp hxinfree hxinhead
        have htaileqsubtail := hxintailimp hxintail
        simp only [Term.substitute, List.map_subtype, List.unattach_attach, Term.func.injEq,
          true_and] at htaileqsubtail
        exact htaileqsubtail hteqsubt

@[simp]
theorem idempotent_iff_inter_empty {sig : Signature} {X : Variables} [BEq X] [BEq sig.funs]
    (σ : Substitution sig X) : Idempotent σ ↔ σ.domain ∩ σ.codomain = ∅ := by
  apply Iff.intro
  -- Forward direction: If σ is idempotent, then its domain and codomain are disjoint.
  · intro hidem
    ext x
    apply Iff.intro
    · simp only [Set.mem_empty_iff_false]
      intro ⟨hxindom, ⟨y, ⟨hyindom, hxinfree⟩⟩⟩
      have hidemy := congr_fun hidem y
      let t := σ y -- construct counterexample
      have hexists : ∃ x ∈ σ.domain, x ∈ t.freeVars := by aesop
      exact Substitution.ne_subst_of_mem_dom_free σ t hexists <| symm hidemy
    · exact fun a ↦ False.elim a
  -- Reverse direction: If the domain and codomain are disjoint, then σ is idempotent.
  · intro h_inter_empty
    have h_disjoint_doms : Disjoint σ.domain σ.codomain := by
      exact Set.disjoint_iff_inter_eq_empty.mpr h_inter_empty
    have h_nindom_of_incodom := Set.disjoint_left.mp (Disjoint.symm h_disjoint_doms)
    rw [Substitution.domain, Substitution.codomain, Set.inter_def] at h_inter_empty
    simp only [Substitution.domain, ne_eq, Substitution.codomain, Set.mem_setOf_eq, Idempotent,
      Substitution] at h_inter_empty
    rw [Set.empty_def] at h_inter_empty
    simp only [Set.setOf_false, Set.eq_empty_iff_forall_not_mem, Set.mem_setOf_eq, not_and,
      not_exists] at h_inter_empty
    funext x
    specialize h_inter_empty x
    by_cases hid : σ x = Term.var x
    · simp_all only [not_true_eq_false, IsEmpty.forall_iff, Substitution.compose, Term.substitute]
    · specialize (h_inter_empty hid) x
      have hxdom : x ∈ σ.domain := by aesop
      have hxninfree := h_inter_empty hxdom
      rw [Substitution.compose]
      refine Substitution.id_of_free_not_in_domain σ (σ x) ?_
      aesop
