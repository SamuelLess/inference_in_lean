import Mathlib.Data.Set.Basic

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

def Symbol := String deriving Repr, DecidableEq

structure SyntFunction where
    symb : Symbol
    arity : ℕ
deriving Repr, DecidableEq

def Constant := {c : SyntFunction // c.arity == 0}

@[simp]
def b : SyntFunction := .mk "b" 0
def b_is_constant : Constant := ⟨b, rfl⟩
@[simp]
def g : SyntFunction := .mk "g" 1

structure SyntPredicate where
    symb : Symbol
    arity: ℕ

def Proposition := {p : SyntPredicate // p.arity == 0}

def P := SyntPredicate.mk "P" 1

structure Signature where
    func : List SyntFunction
    pred : List SyntPredicate

@[simp]
def example_signature : Signature := ⟨[b, g], [P]⟩

/-
--TODO: Find out whether allowing finite variable lists is a problem
Instead this could use a Set and then (h: x ∈ X) is added to the variable constructor in the terms.
-/
def Variables := Type
def Variable : Variables := String deriving Repr, DecidableEq, BEq


inductive Term {sig : Signature} {X : Variables} where
    | var (x: X)
    | func (f: SyntFunction) (args: List (@Term sig X))
           (h : f ∈ sig.func) -- (h': args.length = f.arity) -- this would be perfect

/-
See `LoVe06_InductivePredicates`
-/
inductive HasValidArity {sig : Signature} {X : Variables} [BEq X] : @Term sig X -> Prop
    | var : HasValidArity (@Term.var sig X _)
    | func {args : List Term}
           {func : SyntFunction}
           (h_in: func ∈ sig.func)
           (h_arity: func.arity == args.length)
           (h': ∀t ∈ args, HasValidArity t) : HasValidArity (@Term.func sig X func args h_in)

def ValidTerm {sig : Signature} {X : Variables} [BEq X] := {t : @Term sig X // HasValidArity t}


def ex_valid_term : @ValidTerm example_signature Variable _ :=
    ⟨Term.func b [] (by simp), HasValidArity.func (by simp) (by simp) (by simp)⟩

/-
> g(b)
-/
def ex_valid_term' : @ValidTerm example_signature Variable _ :=
    ⟨Term.func g [ex_valid_term.val] (by simp),
        HasValidArity.func (by simp) (by simp)
            (by simp; exact ex_valid_term.prop)⟩
-- this is so tedieous...

def ex_valid_term'' : @ValidTerm example_signature Variable _:=
    ⟨Term.var "x", HasValidArity.var⟩

inductive IsGround {sig : Signature} {X : Variables}: Term -> Prop
    | func {args : List Term}
           (h: ∀t ∈ args, IsGround t): IsGround (@Term.func sig X _ args _)

/-
By T_Σ we denote the set of Σ-ground terms.
TODO: how can we leave out the X?
-/
def GroundTerm {sig : Signature} {X: Variables} [BEq X] := {t : @Term sig X // HasValidArity t ∧ IsGround t}

-- TODO: build all of this up with the `ValidTerm`
inductive Atom {sig: Signature} {X : Variables} where
    | pred (p: SyntPredicate) (args: List (@Term sig X)) (h_in: p ∈ sig.pred)
    | eq (lhs rhs: @Term sig X)

inductive Literal {sig: Signature} {X: Variables} where
    | pos (a: @Atom sig X)
    | neg (a: @Atom sig X)

def Clause {sig: Signature} {X: Variables} := List (@Literal sig X)

inductive Formula {sig: Signature} {X: Variables} where
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

/-
### Example Peano Arithmetic
-/
def zero : SyntFunction := SyntFunction.mk "0" 0
def s : SyntFunction := SyntFunction.mk "s" 1
def plus : SyntFunction := SyntFunction.mk "+" 2
def times : SyntFunction := SyntFunction.mk "*" 2

def less_than : SyntPredicate := SyntPredicate.mk "<" 2

@[simp]
def ex_sig_peano : Signature := ⟨[zero, s, plus, times], [less_than]⟩

/-
> ∀x, y ((x < y ∨ x ≈ y) ↔ ∃z (x + z ≈ y))
-/
def example_formula_peano : @Formula ex_sig_peano Variable :=
    .all "x" (.all "y" (.iff
        (.or
            (.atom (.pred less_than [.var "x", .var "y"] (by simp)))
            (.atom (.eq (.var "x") (.var "y")))
        )
        (.ex "z"
            (.atom (.eq (.func plus [.var "x", .var "z"] (by simp)) (.var "y")))
        )
    ))


/-
## 3.2 Semantics

### Σ-Algebra
> A = (UA, (fA : UA n → UA )f/n∈Ω , (PA ⊆ UA m )P/m∈Π )
-/

def Universes := Type

structure FuncInter
    (sig: Signature) (univ : Universes) (f : SyntFunction) where
    h_in : f ∈ sig.func
    interpreted : List univ → univ

structure PredInter
    (sig: Signature) (univ : Universes) (p : SyntPredicate) where
    h_in : p ∈ sig.pred
    interpreted : List univ → Prop
/-
A = (UA , (fA : UA n → UA )f/n∈Ω , (PA ⊆ UA m )P/m∈Π )
Again this missses to check the arity of the functions and predicates.
-/
structure Interpretation (sig: Signature) where
    univ : Universes -- specific universe for the interpretation
    functions : ∀ f ∈ sig.func, FuncInter sig univ f
    predicates : ∀ p ∈ sig.pred, PredInter sig univ p


def ex_interpret_peano : Interpretation ex_sig_peano :=
    {
      univ := Nat
      functions := λ f h => match f.symb with
        | "0" => ⟨h, λ _ => f.arity⟩
        | "s" => ⟨h, λ x => x[0]! + 1⟩ -- TODO: figure out how to use the arity
        | "+" => ⟨h, λ args  => args[0]! + args[1]!⟩
        | "*" => ⟨h, λ args => args[0]! * args[1]!⟩
        | _ => ⟨h, λ _ => 0⟩, -- make it total but dont use it
      predicates := λ p h => match p.symb with
        | "<" => ⟨h, λ args => args[0]! < args[1]!⟩
        | _ => ⟨h, λ _ => false⟩ -- make it total but dont use it
    }


def add_one_list : List ℕ -> ℕ
    | [] => 1
    | x :: xs => x + add_one_list xs

/-
### Assigments
> β : X → univ
-/

def Assignment (X: Variables) (univ: Universes) := X → univ

def Assignment.update {X: Variables} {univ: Universes} [BEq X]
                      (β: Assignment X univ) (x: X) (a: univ) : Assignment X univ :=
    λ y => if y == x then a else β y

def ex_assig_peano : Assignment Variable Nat
    | "x" => 21 -- this is kind of a shortcut for `s ... s zero`
    | "y" => 42 -- this is kind of a shortcut for `s zero`
    | _ => 0

mutual
    def evalTerm {sig: Signature} {X: Variables}
                (I: Interpretation sig) (β: Assignment X I.univ) : @Term sig X -> I.univ
        | Term.var x => β x
        | Term.func f args h => (I.functions f h).interpreted $ eval_subterm I β args
    def eval_subterm {sig: Signature} {X: Variables}
                (I: Interpretation sig) (β: Assignment X I.univ) : List (@Term sig X) -> List I.univ
        | [] => []
        | x :: xs => (evalTerm I β x) :: eval_subterm I β xs
end

#eval @evalTerm ex_sig_peano Variable ex_interpret_peano ex_assig_peano (Term.var "y")

def ex_term_peano : @Term ex_sig_peano Variable :=
    Term.func plus [Term.var "x", Term.var "y"] (by simp)

#eval @evalTerm ex_sig_peano Variable ex_interpret_peano ex_assig_peano ex_term_peano

def evalAtom {sig: Signature} {X: Variables}
             (I: Interpretation sig) (β: Assignment X I.univ) : @Atom sig X -> Prop
    | Atom.pred p args h => (I.predicates p h).interpreted (args.map (evalTerm I β))
    | Atom.eq lhs rhs => evalTerm I β lhs = evalTerm I β rhs


@[simp]
def evalFormula {sig: Signature} {X: Variables} [BEq X]
                (I: Interpretation sig) (β: Assignment X I.univ) : @Formula sig X -> Prop
    | Formula.falsum => False
    | Formula.verum => True
    | Formula.atom a => evalAtom I β a
    | Formula.neg f => ¬ evalFormula I β f
    | Formula.and f g => evalFormula I β f ∧ evalFormula I β g
    | Formula.or f g => evalFormula I β f ∨ evalFormula I β g
    | Formula.imp f g => evalFormula I β f → evalFormula I β g
    | Formula.iff f g => evalFormula I β f ↔ evalFormula I β g
    | Formula.all x f => ∀ a : I.univ, evalFormula I (β.update x a) f
    | Formula.ex x f => ∃ a : I.univ, evalFormula I (β.update x a) f

/-
TODO: One of the examples from the script
-/


/-
## 3.3 Models, Validity, and Satisfiability

### Σ-Algebra A with assignment β
> I, β ⊨ F :⇔ I(β)(F) = True
-/

@[simp]
def EntailsInterpret {sig : Signature} {X: Variables} [BEq X]
            (I : @Interpretation sig) (β : Assignment X I.univ) (F : @Formula sig X) : Prop :=
    evalFormula I β F

-- TODO: figure out why this does not work `Decidable`?
--#eval! @evalFormula ex_sig_peano Variable _ ex_interpret_peano ex_assig_peano example_formula_peano

/-example : @EntailsInterpret ex_sig_peano Variable _ ex_interpret_peano
            ex_assig_peano example_formula_peano := by
                simp [ex_sig_peano, ex_interpret_peano, ex_assig_peano, example_formula_peano]
                intro univ
                --simp [evalAtom]
                intro a
                intro c
                sorry
                sorry
-/

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
        evalFormula I β F

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
    {sig : Signature} {X : Variables} [inst : BEq X] (F G : Formula) :
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
Proposition 3.3.3 Let F and G be formulas, let N be a set of formulas. Then
(i) F is valid if and only if ¬F is unsatisfiable.
(ii) F |= G if and only if F ∧ ¬G is unsatisfiable.
-/

theorem valid_iff_not_unsat
    {sig : Signature} {X : Variables} [inst : BEq X] (F : Formula) :
    Valid F ↔ @Unsatisfiable sig X inst (Formula.neg F) := by
        simp

theorem entails_iff_and_not_unsat
    {sig : Signature} {X : Variables} [inst : BEq X] (F G : Formula) :
    Entails F G ↔ @Unsatisfiable sig X inst (Formula.and F (Formula.neg G)) := by
        simp

/-
Expand this to sets of Formulas
-/

@[simp]
def SetEntails {sig : Signature} {X: Variables} [BEq X]
            (N : Set (@Formula sig X)) (F : @Formula sig X) : Prop :=
    ∀ (I : @Interpretation sig) (β : Assignment X I.univ),
        (∀ G ∈ N, EntailsInterpret I β G) → EntailsInterpret I β F

theorem entails_setEntails
    {sig : Signature} {X : Variables} [inst : BEq X] (F G : Formula) :
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
    {sig : Signature} {X : Variables} [inst : BEq X] (F : Formula) :
       Satisfiable F → @SetSatisfiable sig X inst {F} :=
       by simp only [Satisfiable, EntailsInterpret, SetSatisfiable, Set.mem_singleton_iff,
         forall_eq, imp_self]

lemma unsat_as_set_unsat
    {sig : Signature} {X : Variables} [inst : BEq X] (F : Formula) :
       Unsatisfiable F → @SetUnsatisfiable sig X inst {F} :=
       by simp
/-
-- TODO: finish this proof
(iii) N |= G if and only if N ∪ {¬G} is unsatisfiable.
-/
theorem setEntails_iff_union_not_unsat
    {sig : Signature} {X : Variables} [inst : BEq X] (N : Set Formula) (G : Formula) :
    SetEntails N G ↔ @SetUnsatisfiable sig X inst (N ∪ {Formula.neg G}) := by
        sorry


/-
## Further stuff:
- Compactness

-/
