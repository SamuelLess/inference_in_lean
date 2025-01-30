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
    funs : Type
    preds : Type

def Variables := Type

inductive Term (sig : Signature) (X : Variables) where
    | var (x: X)
    | func (f: sig.funs)
           (args: List (Term sig X))

def Term.freeVars {sig : Signature} {X: Variables} : @Term sig X -> Set X
    | .var x => {x}
    | .func _ [] => ∅
    | .func f (a :: args) => Term.freeVars a ∪ Term.freeVars (Term.func f args)
    -- not using foldl becaus termination...


-- TODO: build all of this up with the `ValidTerm`
inductive Atom (sig : Signature) (X : Variables) where
    | pred (p: sig.preds) (args: List (Term sig X))
    | eq (lhs rhs: Term sig X)

def Atom.freeVars {sig : Signature} {X: Variables} : @Atom sig X -> Set X
    | .pred _ args => args.foldl (λ acc t => acc ∪ Term.freeVars t) ∅
    | .eq lhs rhs => Term.freeVars lhs ∪ Term.freeVars rhs

inductive Literal (sig : Signature) (X : Variables) where
    | pos (a: @Atom sig X)
    | neg (a: @Atom sig X)

def Literal.comp {sig : Signature} {X : Variables} : Literal sig X -> Literal sig X
    | .pos a => .neg a
    | .neg a => .pos a

def Clause (sig: Signature) (X: Variables) := List (Literal sig X)

instance {sig : Signature} {X: Variables} : Membership (Literal sig X) (Clause sig X)
    := List.instMembership

inductive Formula (sig: Signature) (X: Variables) where
    | falsum
    | verum
    | atom (a: @Atom sig X)
    | neg (f: @Formula sig X)
    | and (f g: @Formula sig X)
    | or (f g: @Formula sig X)
    | imp (f g: @Formula sig X)
    | iff (f g: @Formula sig X)
    | all (x: X) (f: @Formula sig X)
    | ex (x: X) (f: @Formula sig X)

inductive Substitution (sig : Signature) (X : Variables) where
    | empty : Substitution sig X
    | cons : Substitution sig X -> X -> Term sig X -> Substitution sig X

def Substitution.apply {sig : Signature} {X : Variables} [BEq X] :=
    λ (σ: Substitution sig X) (x: X) => match σ with
        | Substitution.empty => Term.var x
        | Substitution.cons σ' y a => if y == x then a else σ'.apply x

/-This is basically wrapping the cons constructor. Due to the list-like nature this
does remove the old substitution of x.
This could be rewritten to actually build a new substitution but that seems overkill.-/
def Substitution.modify {sig : Signature} {X : Variables} [BEq X]
       (σ: Substitution sig X) (x: X) (a: Term sig X) : Substitution sig X :=
        Substitution.cons σ x a

def Substitution.domain {sig : Signature} {X : Variables} [BEq X] : Substitution sig X -> Set X
    | Substitution.empty => ∅
    | Substitution.cons σ x _ => {x} ∪ Substitution.domain σ

def Substitution.codomain {sig : Signature} {X : Variables} [BEq X] : Substitution sig X -> Set X
    | Substitution.empty => ∅
    | Substitution.cons σ _ a => a.freeVars ∪ Substitution.codomain σ


@[simp]
def Term.substitute {sig : Signature} {X: Variables} [BEq X]
                (σ: Substitution sig X) : @Term sig X -> Term sig X
    | Term.var x => σ.apply x
    | Term.func f args => Term.func f $ args.attach.map (λ ⟨a, _⟩ => a.substitute σ)



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
structure Interpretation (sig: Signature) where
    univ : Universes -- specific universe for the interpretation
    functions : sig.funs -> (List univ -> univ)
    predicates : sig.preds -> (List univ -> Prop)

/-
### Assigments
> β : X → univ
-/

@[simp]
def Assignment (X: Variables) (univ: Universes) := X → univ

@[simp]
def Assignment.modify {X: Variables} {univ: Universes} [BEq X]
                      (β: Assignment X univ) (x: X) (a: univ) : Assignment X univ :=
    λ y => if y == x then a else β y

@[simp]
def Term.eval {sig: Signature} {X: Variables}
            (I: Interpretation sig) (β: Assignment X I.univ) : @Term sig X -> I.univ
    | Term.var x => β x
    | Term.func f args => (I.functions f) $ args.attach.map (λ ⟨a, _⟩ => Term.eval I β a)


@[simp]
def Atom.substitute {sig : Signature} {X: Variables} [BEq X]
                   (σ: Substitution sig X) : @Atom sig X -> Atom sig X
    | Atom.pred p args => Atom.pred p $ args.map (.substitute σ)
    | Atom.eq lhs rhs => Atom.eq (.substitute σ lhs) (.substitute σ rhs)

@[simp]
def Atom.eval {sig: Signature} {X: Variables}
             (I: Interpretation sig) (β: Assignment X I.univ) : @Atom sig X -> Prop
    | Atom.pred p args => (I.predicates p) (args.map (Term.eval I β))
    | Atom.eq lhs rhs => Term.eval I β lhs = Term.eval I β rhs

@[simp]
def Formula.eval {sig: Signature} {X: Variables} [BEq X]
                (I: Interpretation sig) (β: Assignment X I.univ) : @Formula sig X -> Prop
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


def Formula.freeVars {sig : Signature} {X: Variables} : @Formula sig X -> Set X
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
def Formula.substitute {sig : Signature} {X: Variables} [inst : BEq X] [inst_nonempty : Nonempty X]
                      (σ: Substitution sig X) : @Formula sig X -> @Formula sig X
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
def EntailsInterpret {sig : Signature} {X: Variables} [BEq X]
            (I : @Interpretation sig) (β : Assignment X I.univ) (F : @Formula sig X) : Prop :=
    Formula.eval I β F

theorem not_entails_not {sig : Signature} {X: Variables} [BEq X]
            (I : @Interpretation sig) (β : Assignment X I.univ) (F : @Formula sig X) :
            EntailsInterpret I β F → ¬EntailsInterpret I β (Formula.neg F) :=
              λ a a_1 ↦ a_1 a

/-
### Validity / Tautology
> ⊨ F :⇔ A |= F for all A ∈ Σ-Alg
-/
@[simp]
def Valid {sig : Signature} {X: Variables} [BEq X] (F : @Formula sig X) : Prop :=
    ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
        Formula.eval I β F

/-
### Entailment
F ⊨ G, if for all A ∈ Σ-Alg and β ∈ X → UA, we have A, β |= F ⇒ A, β |= G
-/
@[simp]
def Entails {sig : Signature} {X: Variables} [BEq X]
             (F G : @Formula sig X) : Prop :=
    ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
        EntailsInterpret I β F → EntailsInterpret I β G


/-
### Equivalence

##### Proposition 3.3.1
> F ⊨ G if and only if F → G is valid`
-/
theorem entails_iff_imp_valid
    {sig : Signature} {X : Variables} [inst : BEq X] (F G : Formula sig X) :
    Entails F G ↔ @Valid sig X inst (Formula.imp F G) := Eq.to_iff rfl

/-
### Sat
-/
@[simp]
def Satisfiable {sig : Signature} {X: Variables} [BEq X]
                (F : @Formula sig X) : Prop :=
    ∃ (I : @Interpretation sig) (β : Assignment X I.univ),
        EntailsInterpret I β F

@[simp]
def Unsatisfiable {sig : Signature} {X: Variables} [BEq X]
                (F : @Formula sig X) : Prop := ¬Satisfiable F

/-
Expand this to sets of Formulas
-/
@[simp]
def SetEntails {sig : Signature} {X: Variables} [BEq X]
            (N : Set (Formula sig X)) (F : Formula sig X) : Prop :=
    ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
        (∀ G ∈ N, EntailsInterpret I β G) → EntailsInterpret I β F

lemma entails_setEntails
    {sig : Signature} {X : Variables} [inst : BEq X] (F G : Formula sig X) :
    Entails F G ↔ @SetEntails sig X inst {F} G := by
        simp

@[simp]
def SetSatisfiable {sig : Signature} {X: Variables} [BEq X]
                   (N : Set (@Formula sig X)) : Prop :=
    ∃ (I : @Interpretation sig) (β : Assignment X I.univ),
        ∀ G ∈ N, EntailsInterpret I β G

@[simp]
def SetUnsatisfiable {sig : Signature} {X: Variables} [BEq X]
                     (N : Set (@Formula sig X)) : Prop :=
    ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
        ∃ G ∈ N, ¬EntailsInterpret I β G

lemma sat_as_set_sat
    {sig : Signature} {X : Variables} [inst : BEq X] (F : Formula sig X) :
       Satisfiable F → @SetSatisfiable sig X inst {F} :=
       by simp only [Satisfiable, EntailsInterpret, SetSatisfiable, Set.mem_singleton_iff,
         forall_eq, imp_self]

lemma unsat_as_set_unsat
    {sig : Signature} {X : Variables} [inst : BEq X] (F : Formula sig X) :
       Unsatisfiable F → @SetUnsatisfiable sig X inst {F} :=
       by simp

/-Expand this to Literals and Clauses-/
def Literal.satisfied_by {sig : Signature} {X: Variables} [BEq X]
                         (L : Literal sig X) (I : @Interpretation sig)
                         (β : Assignment X I.univ) : Prop :=
        EntailsInterpret I β (match L with
            | Literal.pos a => Formula.atom a
            | Literal.neg a => Formula.neg (Formula.atom a)
        )

def ClauseSatisfiable {sig : Signature} {X: Variables} [BEq X]
                      (C : Clause sig X) : Prop :=
    ∃ (I : @Interpretation sig) (β : Assignment X I.univ),
        ∃ L : Literal sig X, L ∈ C ∧ L.satisfied_by I β

def ClauseSetSatisfiable {sig : Signature} {X : Variables} [BEq X]
                         (N : Set $ Clause sig X) : Prop :=
    ∃ (I : @Interpretation sig) (β : Assignment X I.univ),
        ∀ C ∈ N, ∃ L, L ∈ C ∧ L.satisfied_by I β

/-
### 3.3.4 Substitution Lemma
- do it later maybe
-/
def Term.compose {sig : Signature} {X : Variables} [BEq X]
                    (I : Interpretation sig) (β: Assignment X I.univ) (σ: Substitution sig X) (t : Term sig X) : I.univ :=
            match t with
            | Term.var x => Term.eval I β (σ.apply x)
            | Term.func f args => I.functions f $ args.attach.map (λ ⟨a, _⟩ => Term.compose I β σ a)

theorem substitution_lemma {sig : Signature} {X : Variables} [BEq X]
                           (I : Interpretation sig) (β: Assignment X I.univ) (σ: Substitution sig X) (t : Term sig X) :
                           Term.eval I β (t.substitute σ) = Term.compose I β σ t := by
                            sorry


/-
### 3.7 Inference Systems and Proofs
-/
structure Inference (sig : Signature) (X : Variables) where
    Premises : Set (Formula sig X)
    Conclusion : Formula sig X

structure InferenceSystem (sig : Signature) (X : Variables) where
    Inferences : List (Inference sig X)

structure Proof {sig : Signature} {X : Variables} (Γ : InferenceSystem sig X) where
    Assumptions : Set (Formula sig X)
    Conclusion : Formula sig X
    Formulas : List (Formula sig X)
    FormulasNonEmpty : Formulas ≠ ∅
    LastFormulaIsConclusion : Formulas.getLast FormulasNonEmpty = Conclusion
    IsValid : ∀ i (hindex : i < Formulas.length),
        Formulas[i] ∈ Assumptions ∨
        ∃ inference ∈ Γ.Inferences,
            Formulas[i] = inference.Conclusion ∧
            ∀ formula ∈ inference.Premises,
                ∃ (j : ℕ) (hjindex : j < i),
                    formula = Formulas[j]

def provability {sig : Signature} {X : Variables} (Γ : InferenceSystem sig X) (N : Set (Formula sig X)) (F : Formula sig X) :=
    ∃ proof : Proof Γ, proof.Assumptions = N ∧ proof.Conclusion = F

def soundness {sig : Signature} {X : Variables} [inst : BEq X] (Γ : InferenceSystem sig X) :=
    ∀ inference ∈ Γ.Inferences, SetEntails inference.Premises inference.Conclusion

def general_soundness {sig : Signature} {X : Variables} [inst : BEq X] (Γ : InferenceSystem sig X) :=
    ∀ (N : Set (Formula sig X)) (F : Formula sig X), provability Γ N F → SetEntails N F

theorem soundness_definitions_are_equivalent {sig : Signature} {X : Variables} [inst : BEq X] (Γ : InferenceSystem sig X) :
        soundness Γ → general_soundness Γ := by
    intro hsound N F hproof A β hgstrue
    rcases hproof with ⟨proof, ⟨hassumptions, hconclusion⟩⟩
    have hproofsequencetrue : ∀ F ∈ proof.Formulas, EntailsInterpret A β F := by
        have hindicestrue : ∀ i (hindex : i < proof.Formulas.length), EntailsInterpret A β proof.Formulas[i] := by
            intro i hlen
            induction' i using Nat.case_strong_induction_on with i ih
            · have hvalid := proof.IsValid 0 hlen
              aesop
            · have hvalid := proof.IsValid (i + 1) hlen
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
        have hfindex : ∃ (i : ℕ) (hindex : i < proof.Formulas.length), F = proof.Formulas[i] := by
            sorry
        aesop
    have hlen : proof.Formulas.length - 1 < proof.Formulas.length := sorry
    have hfconclusion := proof.IsValid (proof.Formulas.length - 1) hlen
    have hfislast : proof.Formulas[proof.Formulas.length - 1] = F := sorry
    rw [hfislast] at hfconclusion
    rcases hfconclusion with hl | hr
    · aesop
    subst hassumptions hconclusion
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
theorem GroundResolutionIsSound {sig : Signature} {X : Variables} [inst : BEq X] {D A C : Formula sig X}
        (Resolution : Inference sig X) (hresolution : Resolution = ⟨{.or D A, .or C (.neg A)}, .or D C⟩)
        (Factorization : Inference sig X) (hfactorization : Factorization = ⟨{.or (.or C A) A}, .or C A⟩)
        (Γ_Resolution : InferenceSystem sig X) (hgamma : Γ_Resolution = ⟨[Resolution, Factorization]⟩)
        : soundness Γ_Resolution := by
    intro inference hinf I β hgstrue
    -- aesop would already close the goal here
    subst hresolution hgamma hfactorization
    simp_all only [EntailsInterpret, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false]
    rcases hinf with hres | hfact
    -- we first show that the resolution inference rule is correct
    · subst hres
      simp_all only [Set.mem_insert_iff, Set.mem_singleton_iff, forall_eq_or_imp, Formula.eval, forall_eq]
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
