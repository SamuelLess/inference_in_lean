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
namespace Syntax

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

@[simp]
def Term.freeVars {sig : Signature} {X : Variables} : @Term sig X -> Set X
  | .var x => {x}
  | .func _ [] => ∅
  | .func f (a :: args) => Term.freeVars a ∪ Term.freeVars (Term.func f args)

-- TODO: build all of this up with the `ValidTerm`
inductive Atom (sig : Signature) (X : Variables) where
  | pred (p : sig.preds) (args : List (Term sig X))
  | eq (lhs rhs : Term sig X)

@[simp]
def Atom.freeVars {sig : Signature} {X : Variables} : @Atom sig X -> Set X
  | .pred _ args => args.foldl (fun acc t => acc ∪ Term.freeVars t) ∅
  | .eq lhs rhs => Term.freeVars lhs ∪ Term.freeVars rhs

inductive Literal (sig : Signature) (X : Variables) where
  | pos (a : @Atom sig X)
  | neg (a : @Atom sig X)

@[simp]
def Literal.comp {sig : Signature} {X : Variables} : Literal sig X -> Literal sig X
  | .pos a => .neg a
  | .neg a => .pos a

@[simp]
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

/--
 Creates formula ∀ x_1 ... x_n, F.
-/
@[simp]
def Formula.bigForall {sig : Signature} {X : Variables} [DecidableEq X]
    (xs : List X) (F : Formula sig X) : Formula sig X :=
  match xs with
  | [] => F
  | x :: xs => .all x (F.bigForall xs)

@[simp]
def Clause.toFormula {sig : Signature} {X : Variables} : @Clause sig X -> @Formula sig X
  | [] => Formula.verum
  | .pos l :: ls => Formula.or (Formula.atom l) (Clause.toFormula ls)
  | .neg l :: ls => Formula.or (Formula.neg (Formula.atom l)) (Clause.toFormula ls)

instance {sig : Signature} {X : Variables} : Coe (Clause sig X) (Formula sig X) :=
  ⟨Clause.toFormula⟩

instance {sig : Signature} {X : Variables} : Coe (Set <| Clause sig X) (Set <| Formula sig X) :=
  ⟨fun N => {Clause.toFormula C | C ∈ N}⟩

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

@[simp]
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
