import Mathlib.Data.Set.Basic

set_option autoImplicit false


/-
### 3.1 Syntax
## Syntax:
- nonlogical symbols (domain-specific)
-> terms, atomic formulas
- logical connectives (domain-independent)
-> Boolean combinations, quantifiers
-/

def Symbol := String deriving Repr, DecidableEq

-- TODO: think about adding arity to Function and Predicate
structure SyntFunction where
    symb : Symbol
deriving Repr, DecidableEq

--def Constant := {c : Function // c.arity == 0}
--def a_is_constant : Constant := ⟨a, rfl⟩

def b := SyntFunction.mk "b"
def g := SyntFunction.mk "g"

structure Predicate where
    symb : Symbol

--def Proposition := {p : Predicate // p.arity == 0}

def P := Predicate.mk "P"

structure Signature where
    func : List SyntFunction
    pred : List Predicate

def example_signature : Signature := ⟨[b, g], [P]⟩


/-
--TODO: Find out whether allowing finite variable lists is a problem
Instead this could use a Set and then (h: x ∈ X) is added to the variable constructor in the terms.
-/
def Variables := Type
def Variable : Variables := String deriving Repr, DecidableEq


inductive Term {sig : Signature} {X : Variables} where
    | var (x: X)
    | func (f: SyntFunction) (args: List (@Term sig X))
           (h : f ∈ sig.func) -- (h': args.length = 5) -- this would be perfect

/-
See `LoVe06_InductivePredicates`
-/
inductive HasValidArity {sig : Signature} {X : Variables} : @Term sig X -> Prop
    | var : HasValidArity (@Term.var sig X _)
    | func {args : List Term}
           {func : SyntFunction}
           --(h_arity: func.arity == args.length)
           (h: func ∈ sig.func)
           (h': ∀t ∈ args, HasValidArity t) : HasValidArity (@Term.func sig X func args h)


def ValidTerm {sig : Signature} {X : Variables} := {t : @Term sig X // HasValidArity t}

-- TODO: how can we leave out the X?
inductive IsGround {sig : Signature} {X : Variables}: Term -> Prop
    | func {args : List Term}
            (h: ∀t ∈ args, IsGround t): IsGround (@Term.func sig X _ args _)

/-
By T_Σ we denote the set of Σ-ground terms.
-/
def GroundTerm {sig : Signature} {X: Variables} := {t : @Term sig X // HasValidArity t ∧ IsGround t}

inductive Atom {sig: Signature} {X : Variables} where
    | pred (p: Predicate) (args: List (@Term sig X)) (h: p ∈ sig.pred)
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
    | all (x: Variable) (f: @Formula sig X)
    | ex (x: Variable) (f: @Formula sig X)

/-
### Example Peano Arithmetic
Arity still missing...
-/
def zero : SyntFunction := SyntFunction.mk "0" --0
def s : SyntFunction := SyntFunction.mk "s" --1
def plus : SyntFunction := SyntFunction.mk "+" --2
def times : SyntFunction := SyntFunction.mk "*" --2

def less_than : Predicate := Predicate.mk "<" --2

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
    (sig: Signature) (univ : Universes) where
    p : Predicate
    h_in : p ∈ sig.pred
    interpreted : List univ → Prop
/-
A = (UA , (fA : UA n → UA )f/n∈Ω , (PA ⊆ UA m )P/m∈Π )
Again this missses to check the arity of the functions and predicates.
-/
structure Interpretation (sig: Signature) where
    univ : Universes -- specific universe for the interpretation
    functions : ∀ f ∈ sig.func, FuncInter sig univ f
    predicates : ∀ p ∈ sig.pred, PredInter sig univ


def ex_interpret_peano : Interpretation ex_sig_peano :=
    {
      univ := Nat
      functions := λ f h => match f.symb with
        | "0" => ⟨h, λ _ => 0⟩
        | "s" => ⟨h, λ x => x[0]! + 1⟩ -- TODO: figure out how to use the arity
        | "+" => ⟨h, λ args => args[0]! + args[1]!⟩
        | "*" => ⟨h, λ args => args[0]! * args[1]!⟩
        | _ => ⟨h, λ _ => 0⟩, -- make it total but dont use it
      predicates := λ p h => ⟨p, h, λ _ => True⟩
    }

/-
### Assigments
> β : X → univ
-/

def Assignment (X: Variables) (univ: Universes) := X → univ

def ex_assig_peano : Assignment Variable Nat
    | "x" => 21 -- this is kind of a shortcut for `s ... s zero`
    | "y" => 42 -- this is kind of a shortcut for `s zero`
    | _ => 0

def evalTerm {sig: Signature} {X: Variables}
             (I: Interpretation sig) (β: Assignment X I.univ) : @Term sig X -> I.univ
    | Term.var x => β x
    | Term.func f args h => (I.functions f h).interpreted (args.map (evalTerm I β))

#eval! @evalTerm ex_sig_peano String ex_interpret_peano ex_assig_peano (Term.var "x")

def ex_term_peano : @Term ex_sig_peano Variable :=
    Term.func plus [Term.var "x", Term.var "y"] (by simp)

#eval! @evalTerm ex_sig_peano Variable ex_interpret_peano ex_assig_peano ex_term_peano

def evalAtom {sig: Signature} {X: Variables}
             (I: Interpretation sig) (β: Assignment X I.univ) : @Atom sig X -> Prop
    | Atom.pred p args h => (I.predicates p h).interpreted (args.map (evalTerm I β))
    | Atom.eq lhs rhs => evalTerm I β lhs = evalTerm I β rhs


/-
## 3.3 Models, Validity, and Satisfiability

### Σ-Algebra A with assignment β
> A, β ⊨ F :⇔ A(β)(F) = 1

### Validity
> ⊨ F :⇔ A |= F for all A ∈ Σ-Alg

### Entailment
F ⊨ G, if for all A ∈ Σ-Alg and β ∈ X → UA, we have A, β |= F ⇒ A, β |= G

### Equivalence

##### Proposition 3.3.1
> F ⊨ G if and only if F → G is valid`

##### Proposition 3.3.2
> F ⊨ G if and only if F ↔ G is valid.`
-/
