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

mutual
  def eqTerm {sig : Signature} {X : Variables} [instX : BEq X] [instF : BEq sig.funs] :
      Term sig X → Term sig X → Bool
    | Term.var x, Term.var y => x == y
    | Term.func f fargs, Term.func g gargs => f == g && eqArgs fargs gargs
    | _, _ => false
  def eqArgs {sig : Signature} {X : Variables} [instX : BEq X] [instF : BEq sig.funs] :
      List (Term sig X) → List (Term sig X) → Bool
    | [], [] => true
    | [], _ => false
    | _, [] => false
    | x :: xs, y :: ys => eqTerm x y && eqArgs xs ys
end

instance {sig : Signature} {X : Variables} [instX : BEq X] [instF : BEq sig.funs] :
    BEq (Term sig X) :=
  ⟨eqTerm⟩

@[simp]
def Term.freeVars {sig : Signature} {X : Variables} : Term sig X -> Set X
  | .var x => {x}
  | .func _ [] => ∅
  | .func f (a :: args) => Term.freeVars a ∪ Term.freeVars (Term.func f args)

inductive Atom (sig : Signature) (X : Variables) where
  | pred (p : sig.preds) (args : List (Term sig X))
  | eq (lhs rhs : Term sig X)

@[simp]
def Atom.freeVars {sig : Signature} {X : Variables} : Atom sig X -> Set X
  | .pred _ args => args.foldl (fun acc t => acc ∪ Term.freeVars t) ∅
  | .eq lhs rhs => Term.freeVars lhs ∪ Term.freeVars rhs

inductive Literal (sig : Signature) (X : Variables) where
  | pos (a : Atom sig X)
  | neg (a : Atom sig X)

@[simp]
def Literal.comp {sig : Signature} {X : Variables} : Literal sig X -> Literal sig X
  | .pos a => .neg a
  | .neg a => .pos a

@[simp]
def Clause (sig : Signature) (X : Variables) := List (Literal sig X)

instance {sig : Signature} {X : Variables} : Membership (Literal sig X) (Clause sig X) :=
  List.instMembership

instance {sig : Signature} {X : Variables} : Append (Clause sig X) :=
  List.instAppend

instance {sig : Signature} {X : Variables} : HAppend (Clause sig X) (Clause sig X) (Clause sig X) :=
  instHAppendOfAppend

inductive Formula (sig: Signature) (X: Variables) where
  | falsum
  | verum
  | atom (a : Atom sig X)
  | neg (f : Formula sig X)
  | and (f g : Formula sig X)
  | or (f g : Formula sig X)
  | imp (f g : Formula sig X)
  | iff (f g : Formula sig X)
  | all (x : X) (f : Formula sig X)
  | ex (x : X) (f : Formula sig X)

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
def Clause.toFormula {sig : Signature} {X : Variables} : Clause sig X -> Formula sig X
  | [] => Formula.falsum
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
    Term sig X -> Term sig X
  | Term.var x => σ x
  | Term.func f args => Term.func f <| args.attach.map (fun ⟨a, _⟩ => a.substitute σ)

@[simp]
def Atom.substitute {sig : Signature} {X : Variables} (σ : Substitution sig X) :
    Atom sig X -> Atom sig X
  | Atom.pred p ts => Atom.pred p (ts.map (Term.substitute σ))
  | Atom.eq lhs rhs => Atom.eq (lhs.substitute σ) (rhs.substitute σ)

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

/-
Maybe continue with?
3.3 LEMMA If a is an idempotent substitution and z is an arbitrary substitution, then a is
more general than z iff za = z.
-/
