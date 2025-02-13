import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Range

set_option autoImplicit false
--set_option diagnostics true

/-
## 3.1 Syntax
### Syntax:
- nonlogical symbols (domain-specific)
-> terms, atomic formulas
- logical connectives (domain-independent)
-> Boolean combinations, quantifiers
-/
namespace FirstOrder

structure Signature where
  /-- The type of the syntactic function symbols -/
  funs : Type
  /-- The type of the syntactic predicate symbols -/
  preds : Type

def Variables := Type

inductive Term (sig : Signature) (X : Variables) where
  | var (x : X)
  | func (f : sig.funs) (args: List (Term sig X))

lemma Term.induction {sig : Signature} {X : Variables} {P : (Term sig X) → Prop}
    (base : ∀ x : X, P (var x)) (step : ∀ (args : List (Term sig X)),
      (ih : ∀ term ∈ args, P term) → ∀ (f : sig.funs), P (func f args)) :
    ∀ (t : Term sig X), P t := by
  intro t
  match t with
  | var x => aesop
  | func f args =>
    apply step
    intro term harg
    apply Term.induction
    · exact base
    · intro args' ih f'
      apply step
      intro term' harg'
      exact ih term' harg'

def Term.freeVars {sig : Signature} {X : Variables} : @Term sig X -> Set X
  | .var x => {x}
  | .func _ [] => ∅
  | .func f (a :: args) => Term.freeVars a ∪ Term.freeVars (Term.func f args)

-- TODO: build all of this up with the `ValidTerm`
inductive Atom (sig : Signature) (X : Variables) where
  | pred (p : sig.preds) (args : List (Term sig X))
  | eq (lhs rhs : Term sig X)

def Atom.freeVars {sig : Signature} {X : Variables} : @Atom sig X -> Set X
  | .pred _ args => args.foldl (fun acc t => acc ∪ Term.freeVars t) ∅
  | .eq lhs rhs => Term.freeVars lhs ∪ Term.freeVars rhs

inductive Literal (sig : Signature) (X : Variables) where
  | pos (a : @Atom sig X)
  | neg (a : @Atom sig X)

def Literal.comp {sig : Signature} {X : Variables} : Literal sig X -> Literal sig X
  | .pos a => .neg a
  | .neg a => .pos a

def Clause (sig : Signature) (X : Variables) := List (Literal sig X)

instance {sig : Signature} {X : Variables} : Membership (Literal sig X) (Clause sig X) :=
  List.instMembership

inductive Formula (sig: Signature) (X: Variables) where
  | falsum
  | verum
  | atom (a : @Atom sig X)
  | neg (f : @Formula sig X)
  | and (f g : @Formula sig X)
  | or (f g : @Formula sig X)
  | imp (f g : @Formula sig X)
  | iff (f g : @Formula sig X)
  | all (x : X) (f : @Formula sig X)
  | ex (x : X) (f : @Formula sig X)

@[simp]
def Substitution (sig : Signature) (X : Variables) := X -> Term sig X

@[simp]
def Substitution.modify {sig : Signature} {X : Variables} [DecidableEq X]
    (σ : Substitution sig X) (x : X) (a : Term sig X) : Substitution sig X :=
  fun y => if y = x then a else σ y

@[simp]
def Term.substitute {sig : Signature} {X : Variables} (σ : Substitution sig X) :
    @Term sig X -> Term sig X
  | Term.var x => σ x
  | Term.func f args => Term.func f <| args.attach.map (fun ⟨a, _⟩ => a.substitute σ)

@[simp]
def Substitution.compose {sig : Signature} {X : Variables} (σ τ: Substitution sig X) :
    Substitution sig X :=
  fun x => (τ x).substitute σ
infix:90 " ∘ " => Substitution.compose

def Substitution.domain {sig : Signature} {X : Variables} (σ : Substitution sig X) : Set X :=
  {x : X | σ x ≠ Term.var x}

def Substitution.codomain {sig : Signature} {X : Variables} (σ : Substitution sig X) : Set X :=
  {x : X | ∃ y : X, y ∈ σ.domain ∧ x ∈ (σ y).freeVars}

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

def Idempotent {sig : Signature} {X : Variables} [BEq X] (σ : Substitution sig X) : Prop :=
  σ ∘ σ = σ

theorem idempotent_iff_empty_interesec {sig : Signature} {X : Variables} [BEq X]
    (σ : Substitution sig X) : Idempotent σ ↔ σ.domain ∩ σ.codomain = ∅ := by
  -- Construct the equivalence by proving both directions.
  apply Iff.intro
  -- Forward direction: If σ is idempotent, then its domain and codomain are disjoint.
  · intro h
    ext x
    -- Simplify the membership conditions for the intersection of domain and codomain.
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    -- Introduce a helper lemma to handle the case where x is in both domain and codomain.
    intro ⟨hxdom, hxcodom⟩
    -- Use the idempotence property to derive a contradiction.
    have h1 := congr_fun h x
    simp [Substitution.domain] at hxdom
    simp [Substitution.codomain] at hxcodom
    obtain ⟨y, ⟨hy, hxy⟩⟩ := hxcodom
    -- σ={x ↦ y, z ↦ x} => σ.dom = {x, z}, σ.codom = {y, x} => x ∈ σ.codom
    -- x maps to something that is not x
    -- something maps to x
    -- so applying once
    -- use that σ z != (σ ∘ σ) z
    sorry
  -- Reverse direction: If the domain and codomain are disjoint, then σ is idempotent.
  · intro h
    sorry

/-
## 3.2 Semantics

### Σ-Algebra
> A = (UA, (fA : UA n → UA )f/n∈Ω , (PA ⊆ UA m )P/m∈Π )
-/

def Universes := Type
/-
A = (UA , (fA : UA n → UA )f/n∈Ω , (PA ⊆ UA m )P/m∈Π )
Again this missses to check the arity of the functions and predicates.
-/
structure Interpretation (sig : Signature) where
  univ : Universes
  functions : sig.funs -> (List univ -> univ)
  predicates : sig.preds -> (List univ -> Prop)

/-
### Assigments
> β : X → univ
-/

@[simp]
def Assignment (X : Variables) (univ : Universes) := X → univ

@[simp]
def Assignment.modify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (x : X) (a : univ) : Assignment X univ :=
  fun y => if y = x then a else β y

@[simp]
def Term.eval {sig : Signature} {X : Variables}
    (I : Interpretation sig) (β : Assignment X I.univ) : @Term sig X -> I.univ
  | Term.var x => β x
  | Term.func f args => (I.functions f) <| args.attach.map (fun ⟨a, _⟩ => Term.eval I β a)


@[simp]
def Atom.substitute {sig : Signature} {X : Variables} [DecidableEq X]
    (σ : Substitution sig X) : @Atom sig X -> Atom sig X
  | Atom.pred p args => Atom.pred p <| args.map (.substitute σ)
  | Atom.eq lhs rhs => Atom.eq (.substitute σ lhs) (.substitute σ rhs)

@[simp]
def Atom.eval {sig : Signature} {X : Variables}
    (I : Interpretation sig) (β : Assignment X I.univ) : @Atom sig X -> Prop
  | Atom.pred p args => (I.predicates p) (args.map (Term.eval I β))
  | Atom.eq lhs rhs => Term.eval I β lhs = Term.eval I β rhs

@[simp]
def Formula.eval {sig : Signature} {X : Variables} [DecidableEq X]
    (I : Interpretation sig) (β : Assignment X I.univ) : @Formula sig X -> Prop
  | Formula.falsum => False
  | Formula.verum => True
  | Formula.atom a => Atom.eval I β a
  | Formula.neg f => ¬ Formula.eval I β f
  | Formula.and f g => Formula.eval I β f ∧ Formula.eval I β g
  | Formula.or f g => Formula.eval I β f ∨ Formula.eval I β g
  | Formula.imp f g => Formula.eval I β f → Formula.eval I β g
  | Formula.iff f g => Formula.eval I β f ↔ Formula.eval I β g
  | Formula.all x f => ∀ a : I.univ, Formula.eval I (β.modify x a) f
  | Formula.ex x f => ∃ a : I.univ, Formula.eval I (β.modify x a) f

@[simp]
def Formula.freeVars {sig : Signature} {X : Variables} : @Formula sig X -> Set X
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


/-
TODO: take care of bound variables in quantifiers or maybe just dont care?
(Qx F)σ = Qz (F σ[x → z]) with z a fresh variable and Q ∈ {∀, ∃}
However, how can we cleanly ensure that z is fresh?
Do we even need to? Let's not do it now and mabye add some hypothesis for the substiution later.
This should force drastic modifications of everything buildng on this (fingers crossed).
-/
@[simp]
def Formula.substitute {sig : Signature} {X : Variables}
    [inst : DecidableEq X] [inst_nonempty : Nonempty X]
    (σ : Substitution sig X) : @Formula sig X -> @Formula sig X
  | Formula.falsum => Formula.falsum
  | Formula.verum => Formula.verum
  | Formula.atom a => Formula.atom (Atom.substitute σ a)
  | Formula.neg f => Formula.neg (substitute σ f)
  | Formula.and f g => Formula.and (substitute σ f) (substitute σ g)
  | Formula.or f g => Formula.or (substitute σ f) (substitute σ g)
  | Formula.imp f g => Formula.imp (substitute σ f) (substitute σ g)
  | Formula.iff f g => Formula.iff (substitute σ f) (substitute σ g)
  | Formula.all x f => Formula.all x (substitute σ f)
  | Formula.ex x f => Formula.all x (substitute σ f)


/-
## 3.3 Models, Validity, and Satisfiability

### Σ-Algebra A with assignment β
> I, β ⊨ F :⇔ I(β)(F) = True
-/

@[simp]
def EntailsInterpret {sig : Signature} {X: Variables} [DecidableEq X]
    (I : @Interpretation sig) (β : Assignment X I.univ) (F : @Formula sig X) : Prop :=
  Formula.eval I β F

theorem not_entails_not {sig : Signature} {X : Variables} [DecidableEq X]
    (I : @Interpretation sig) (β : Assignment X I.univ) (F : @Formula sig X) :
    EntailsInterpret I β F → ¬EntailsInterpret I β (Formula.neg F) :=
  fun a a_1 ↦ a_1 a

/-
### Validity / Tautology
> ⊨ F :⇔ A |= F for all A ∈ Σ-Alg
-/
@[simp]
def Valid {sig : Signature} {X : Variables} [DecidableEq X] (F : @Formula sig X) : Prop :=
  ∀ (I : @Interpretation sig) (β : Assignment X I.univ), Formula.eval I β F

/-
### Entailment
F ⊨ G, if for all A ∈ Σ-Alg and β ∈ X → UA, we have A, β |= F ⇒ A, β |= G
-/
@[simp]
def Entails {sig : Signature} {X : Variables} [DecidableEq X] (F G : @Formula sig X) : Prop :=
  ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
    EntailsInterpret I β F → EntailsInterpret I β G
infix:60 " ⊨ " => Entails


/-
### Equivalence

##### Proposition 3.3.1
> F ⊨ G if and only if F → G is valid`
-/
theorem entails_iff_imp_valid {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F G : Formula sig X) : Entails F G ↔ @Valid sig X inst (Formula.imp F G) :=
  Eq.to_iff rfl


/-
### Sat
-/
@[simp]
def Satisfiable {sig : Signature} {X : Variables} [DecidableEq X] (F : @Formula sig X) : Prop :=
  ∃ (I : @Interpretation sig) (β : Assignment X I.univ), EntailsInterpret I β F

@[simp]
def Unsatisfiable {sig : Signature} {X : Variables} [DecidableEq X] (F : @Formula sig X) : Prop :=
  ¬Satisfiable F

theorem valid_iff_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F : Formula sig X) : Valid F ↔ @Unsatisfiable sig X inst (Formula.neg F) := by simp

theorem entails_iff_and_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F G : Formula sig X) :
    Entails F G ↔ @Unsatisfiable sig X inst (Formula.and F (Formula.neg G)) := by simp

/-
Expand this to sets of Formulas
-/
@[simp]
def SetEntails {sig : Signature} {X : Variables} [DecidableEq X]
    (N : Set (Formula sig X)) (F : Formula sig X) : Prop :=
  ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
    (∀ G ∈ N, EntailsInterpret I β G) → EntailsInterpret I β F

lemma entails_setEntails {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F G : Formula sig X) : Entails F G ↔ @SetEntails sig X inst {F} G := by simp

@[simp]
def SetSatisfiable {sig : Signature} {X : Variables} [DecidableEq X]
    (N : Set (@Formula sig X)) : Prop :=
  ∃ (I : @Interpretation sig) (β : Assignment X I.univ), ∀ G ∈ N, EntailsInterpret I β G

@[simp]
def SetUnsatisfiable {sig : Signature} {X : Variables} [DecidableEq X]
    (N : Set (@Formula sig X)) : Prop :=
  ∀ (I : @Interpretation sig) (β : Assignment X I.univ), ∃ G ∈ N, ¬EntailsInterpret I β G

lemma sat_as_set_sat {sig : Signature} {X : Variables} [inst : DecidableEq X] (F : Formula sig X) :
    Satisfiable F → @SetSatisfiable sig X inst {F} :=
  by simp only [Satisfiable, Assignment, EntailsInterpret, SetSatisfiable, Set.mem_singleton_iff,
    forall_eq, imp_self]

lemma unsat_as_set_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F : Formula sig X) : Unsatisfiable F → @SetUnsatisfiable sig X inst {F} := by simp

theorem setEntails_iff_union_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (N : Set $ Formula sig X) (G : Formula sig X) :
    SetEntails N G ↔ @SetUnsatisfiable sig X inst (N ∪ {Formula.neg G}) := by
        sorry

/-Expand this to Literals and Clauses-/
def Literal.satisfied_by {sig : Signature} {X: Variables} [DecidableEq X]
    (L : Literal sig X) (I : @Interpretation sig) (β : Assignment X I.univ) : Prop :=
  EntailsInterpret I β <| match L with
    | Literal.pos a => Formula.atom a
    | Literal.neg a => Formula.neg (Formula.atom a)

def ClauseSatisfiable {sig : Signature} {X : Variables} [DecidableEq X] (C : Clause sig X) : Prop :=
  ∃ (I : @Interpretation sig) (β : Assignment X I.univ),
    ∃ L : Literal sig X, L ∈ C ∧ L.satisfied_by I β

def ClauseSetSatisfiable {sig : Signature} {X : Variables} [DecidableEq X]
    (N : Set <| Clause sig X) : Prop :=
  ∃ (I : @Interpretation sig) (β : Assignment X I.univ), ∀ C ∈ N, ∃ L, L ∈ C ∧ L.satisfied_by I β

/-
### 3.3.4 Substitution Lemma
- do it later maybe
-/
@[simp]
def Assignment.compose {sig : Signature} {X : Variables} [DecidableEq X]
    (I : Interpretation sig) (β : Assignment X I.univ) (σ : Substitution sig X) (t : Term sig X) :
    I.univ :=
  match t with
  | Term.var x => Term.eval I β (σ x)
  | Term.func f args => I.functions f <| args.attach.map (fun ⟨a, _⟩ => Assignment.compose I β σ a)

theorem substitution_lemma {sig : Signature} {X : Variables} [DecidableEq X]
    (I : Interpretation sig) (β : Assignment X I.univ) (σ : Substitution sig X) (t : Term sig X) :
    Term.eval I β (t.substitute σ) = Assignment.compose I β σ t := by
  match t with
  | .var x => aesop
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
theorem substitution_lemma' {sig : Signature} {X : Variables} [DecidableEq X]
    (I : Interpretation sig) (β : Assignment X I.univ) (σ : Substitution sig X) (t : Term sig X) :
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


-- for variables x_1,...,x_n and formula F, this returns ∀ x_1 ... x_n, F
@[simp]
def Formula.BigForall {sig : Signature} {X : Variables} [DecidableEq X]
    (xs : List X) (F : Formula sig X) : Formula sig X :=
  match xs with
  | [] => F
  | x :: xs => .all x (Formula.BigForall xs F)

@[simp]
def BigModify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (modifications : List (X × univ)) : Assignment X univ :=
  match modifications with
  | [] => β
  | (x, a) :: modifications => BigModify (β.modify x a) modifications

/-
### Lemma 3.3.7
-/
lemma substitute_equality {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) :
    β = BigModify β (xs.zip (xs.map β)) := by
  have hsubeq : β = BigModify β (xs.zipWith Prod.mk (xs.map β)) := by
    induction' xs with x xs ih
    · aesop
    · have hlen : xs.length = (xs.map β).length := by exact Eq.symm (List.length_map xs β)
      rw [List.map, List.zipWith, BigModify]
      have hsubeq : β.modify x (β x) = β := by
        funext y
        rw [Assignment.modify]
        split_ifs with h
        · rw [h]
        · rfl
      rw [hsubeq, ← ih]
  induction' xs with x xs ih
  · aesop
  · rw [List.zip, ← hsubeq]

#check List.mem_iff_getElem
#check List.Nodup
#check List.findIdx
--lemma IndexedFinset.mem_iff_getElem {α : Type} {n : ℕ} {ifset : IndexedFinset α n}

noncomputable def index_map {α β: Type} [DecidableEq α] (f : α → β)
    (as : List α) (bs : List β) (hlen : as.length = bs.length):
    α → β :=
  fun a ↦ if hmem: a ∈ as then by
    have hindex := List.mem_iff_getElem.mp hmem
    let hchoice := Exists.choose_spec hindex
    have hinbounds := Exists.choose hchoice
    set i := hindex.choose with heq
    rw [hlen] at hinbounds
    exact bs[i]
  else
    f a

lemma three_three_seven {sig : Signature} {X : Variables} [DecidableEq X]
    (F : Formula sig X) (xs : List X) (hfree : ∀ x ∈ xs, x ∈ F.freeVars):
    Valid (Formula.BigForall xs F) ↔ Valid F := by
  apply Iff.intro
  · intro hvalid I γ
    specialize hvalid I
    have hlemma (as : List I.univ) :
        F.eval I (BigModify γ (xs.zipWith Prod.mk as)) := by
      induction' xs with x xs ih generalizing as
      · aesop
      · rw [Formula.BigForall] at *
        simp_all only [List.mem_cons, or_true, implies_true, Assignment, forall_const,
          forall_eq_or_imp, Formula.eval]
        obtain ⟨hfree, hallfree⟩ := hfree
        --specialize hvalid γ
        induction' as with a as ih' generalizing xs
        · rw [List.zipWith]
          · simp_all only [BigModify]
            sorry
          · aesop
        · rw [List.zipWith, BigModify]
          specialize hvalid
          specialize ih sorry as
          sorry
    set as : List I.univ := List.map γ xs with has
    have hsubequal : γ = BigModify γ (List.zip xs as) := by
      exact substitute_equality γ xs
    rw [hsubequal]
    apply hlemma as
  · intro hvalid I
    induction' xs <;> aesop

/-
### Unification
-/

@[simp]
def Equality (sig : Signature) (X : Variables) :=
  Term sig X × Term sig X

@[simp]
def EqualityProblem (sig : Signature) (X : Variables) :=
  List (Equality sig X)

instance {sig : Signature} {X : Variables} : Membership (Equality sig X) (EqualityProblem sig X) :=
  List.instMembership

def EqualityProblem.freeVars {sig : Signature} {X : Variables} :
    @EqualityProblem sig X -> Set X
  | [] => ∅
  | (lhs, rhs) :: eqs => Term.freeVars lhs ∪ Term.freeVars rhs ∪ freeVars eqs

@[simp]
def Unifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : @EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  ∀ eq ∈ E, have ⟨lhs, rhs⟩ := eq; lhs.substitute σ = rhs.substitute σ

def example_unification_problem : EqualityProblem (Signature.mk String String) String :=
  [(.func "f" [Term.var "x"], Term.var "y")]

def example_unifier : Substitution (Signature.mk String String) String :=
  fun x => if x == "y" then Term.func "f" [Term.var "x"] else Term.var x

theorem example_unification : Unifier example_unification_problem example_unifier := by
  simp [example_unification_problem, example_unifier]

@[simp]
def MostGeneralUnifier {sig : Signature} {X : Variables} [DecidableEq X]
    (E : EqualityProblem sig X) (σ : Substitution sig X) : Prop :=
  Unifier E σ ∧ (∀ τ : Substitution sig X, Unifier E τ → σ ≤ τ)

lemma mgu_imp_unifier {sig : Signature} {X : Variables} [DecidableEq X] (E : EqualityProblem sig X)
    (σ : Substitution sig X) : MostGeneralUnifier E σ → Unifier E σ := fun ⟨h, _⟩ => h

@[simp]
def Unifiable {sig : Signature} {X : Variables} [DecidableEq X]
  (E : EqualityProblem sig X) : Prop := ∃ σ : Substitution sig X, Unifier E σ

theorem unifiable_iff_mgu_idempot {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (E : EqualityProblem sig X) : Unifiable E ↔ ∃ σ : Substitution sig X,
      MostGeneralUnifier E σ ∧ Idempotent σ ∧ σ.domain ∪ σ.codomain ⊆ E.freeVars := by
  apply Iff.intro
  · sorry
  · intro h
    obtain ⟨σ, ⟨⟨⟩⟩⟩ := h
    use σ
alias main_unification_theorem := unifiable_iff_mgu_idempot


/-
### 3.7 Inference Systems and Proofs
-/
structure Inference (sig : Signature) (X : Variables) where
  premises : Set (Formula sig X)
  conclusion : Formula sig X

-- TODO: make this def := List
structure InferenceSystem (sig : Signature) (X : Variables) where
  inferences : List (Inference sig X)

structure Proof {sig : Signature} {X : Variables} (Γ : InferenceSystem sig X) where
  assumptions : Set (Formula sig X)
  conclusion : Formula sig X
  formulas : List (Formula sig X)
  formulas_not_empty : formulas ≠ ∅
  last_formula_conclusion : formulas[formulas.length - 1]'(by
    have hlennonzero : formulas.length ≠ 0 := by
      simp_all only [List.empty_eq, ne_eq, List.length_eq_zero, not_false_eq_true]
    exact Nat.sub_one_lt hlennonzero) = conclusion
  is_valid : ∀ i (hindex : i < formulas.length), formulas[i] ∈ assumptions ∨
    ∃ inference ∈ Γ.inferences, formulas[i] = inference.conclusion ∧
      ∀ formula ∈ inference.premises, ∃ (j : ℕ) (hjindex : j < i), formula = formulas[j]

@[simp]
def Provability {sig : Signature} {X : Variables}
    (Γ : InferenceSystem sig X) (N : Set (Formula sig X)) (F : Formula sig X) : Prop :=
  ∃ proof : Proof Γ, proof.assumptions = N ∧ proof.conclusion = F

@[simp]
def Soundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Prop :=
  ∀ inference ∈ Γ.inferences, SetEntails inference.premises inference.conclusion

@[simp]
def GeneralSoundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Prop :=
  ∀ (N : Set (Formula sig X)) (F : Formula sig X), Provability Γ N F → SetEntails N F

theorem generalSoundness_of_soundness {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (Γ : InferenceSystem sig X) : Soundness Γ → GeneralSoundness Γ := by
  intro hsound N F hproof A β hgstrue
  rcases hproof with ⟨proof, ⟨hassumptions, hconclusion⟩⟩
  have hproofsequencetrue : ∀ F ∈ proof.formulas, EntailsInterpret A β F := by
    have hindicestrue : ∀ i (hindex : i < proof.formulas.length),
        EntailsInterpret A β proof.formulas[i] := by
      intro i hlen
      induction' i using Nat.case_strong_induction_on with i ih
      · have hvalid := proof.is_valid 0 hlen
        aesop
      · have hvalid := proof.is_valid (i + 1) hlen
        rcases hvalid with hassump | hconseq
        · aesop
        · rcases hconseq with ⟨inference, ⟨hin, ⟨hlast, hprev⟩⟩⟩
          rw [hlast]
          have hinfsound := hsound inference hin
          apply hinfsound
          intro inf_form hprem
          have hinftrue := hprev inf_form hprem
          rcases hinftrue with ⟨j, ⟨hjindex, heq⟩⟩
          have hjtrue := ih j (Nat.le_of_lt_succ hjindex) (Nat.lt_trans hjindex hlen)
          rw [heq]
          exact hjtrue
    intro F hF
    have hfindex : ∃ (i : ℕ) (hindex : i < proof.formulas.length), proof.formulas[i] = F :=
      List.mem_iff_getElem.mp hF
    aesop
  have hlen : proof.formulas.length - 1 < proof.formulas.length := by
    have hlennonzero : proof.formulas.length ≠ 0 := by
      have hnonempty := proof.formulas_not_empty
      simp_all only [List.empty_eq, ne_eq, List.length_eq_zero, not_false_eq_true]
    exact Nat.sub_one_lt hlennonzero
  have hfconclusion := proof.is_valid (proof.formulas.length - 1) hlen
  have hfislast : proof.formulas[proof.formulas.length - 1] = F := by
    rw [proof.last_formula_conclusion, hconclusion]
  rw [hfislast] at hfconclusion
  rcases hfconclusion with hl | hr
  · aesop
  · subst hassumptions hconclusion
    obtain ⟨inference, h⟩ := hr
    obtain ⟨hinf, right⟩ := h
    obtain ⟨hconcs, hforms⟩ := right
    have h := hsound inference hinf
    rw [hconcs]
    apply h
    intro G hgprem
    have hinf := hforms G hgprem
    rcases hinf with ⟨j, hjnotconc, hginforms⟩
    aesop

/-
### 3.8 Ground (or Propositional) Resolution
-/

theorem groundResolution_soundness {sig : Signature} {X : Variables} {D A C : Formula sig X}
    [inst : DecidableEq X] (Resolution : Inference sig X)
    (hresolution : Resolution = ⟨{.or D A, .or C (.neg A)}, .or D C⟩)
    (Factorization : Inference sig X)
    (hfactorization : Factorization = ⟨{.or (.or C A) A}, .or C A⟩)
    (Γ_Resolution : InferenceSystem sig X) (hgamma : Γ_Resolution = ⟨[Resolution, Factorization]⟩) :
    Soundness Γ_Resolution := by
  intro inference hinf I β hgstrue
  -- aesop would already close the goal here
  subst hresolution hgamma hfactorization
  simp_all only [EntailsInterpret, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
  rcases hinf with hres | hfact
  -- we first show that the resolution inference rule is correct
  · subst hres
    simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff,
      forall_eq_or_imp, Formula.eval, forall_eq]
    obtain ⟨D_or_A, C_or_notA⟩ := hgstrue
    rcases D_or_A with hD | hA
    · left
      exact hD
    · rcases C_or_notA with hC | hnA
      · right
        exact hC
      · exact False.elim (hnA hA)
  -- next, we show that the factorization inference rule is correct
  · subst hfact
    simp_all only [Set.mem_singleton_iff, Formula.eval, forall_eq]
    rcases hgstrue with (hC | hA) | hA
    · left
      exact hC
    · right
      exact hA
    · right
      exact hA

/-
## Further stuff:
- Compactness

-/
