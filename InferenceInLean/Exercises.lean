import InferenceInLean.Basic
import Mathlib.Data.Finset.Defs

set_option autoImplicit false

open Syntax
open Semantics
open Models
open Unification
open Inferences

namespace Examples

/- ### Example Peano Arithmetic -/

inductive PeanoFuns where
  | zero
  | succ
  | add
  | mul

inductive PeanoPreds where
  | less_than
  | eq

@[simp]
def ex_sig_peano : Signature := ⟨PeanoFuns, PeanoPreds⟩

/-
> ∀x, y ((x < y ∨ x ≈ y) ↔ ∃z (x + z ≈ y))
-/
@[simp]
def ex_formula_peano : @Formula ex_sig_peano String :=
  .all "x" <| .all "y" <| .iff
    (.or
      (.atom (.pred .less_than [.var "x", .var "y"]))
      (.atom (.pred .eq [(.var "x"), (.var "y")])))
    (.ex "z" (.atom (.pred .eq [(.func .add [.var "x", .var "z"]), (.var "y")])))

@[simp]
def ex_interpret_peano : Interpretation ex_sig_peano ℕ where
  functions := λ
    | .zero => λ _ => 0
    | .succ => λ xs => xs[0]! + 1
    | .add => λ xs => xs[0]! + xs[1]!
    | .mul => λ xs => xs[0]! * xs[1]!
  predicates := λ f => match f with
    | .less_than => λ xs => xs[0]! < xs[1]!
    | .eq => λ xs => xs[0]! = xs[1]!

def ex_assig_peano : Assignment String Nat
  | "x" => 0
  | "y" => 0
  | _ => 0

def example_substitution : Substitution ex_sig_peano String := λ x => match x with
  | "x" => Term.func .succ [Term.var "y"]
  | _ => Term.var x

def ex_formula_peano_lt : @Formula ex_sig_peano String :=
  .all "z" (.atom $ .pred .less_than [.var "x", .func .succ [.func .succ [.var "z"]]])

lemma ex_proof_lt : @Formula.eval ex_sig_peano String ℕ instDecidableEqString
    ex_interpret_peano ex_assig_peano ex_formula_peano_lt := by
  simp [ex_formula_peano_lt, ex_sig_peano, Interpretation, Assignment, ex_assig_peano]


#eval @Term.eval ex_sig_peano String ℕ ex_interpret_peano ex_assig_peano (Term.var "y")

def ex_term_peano : Term ex_sig_peano String :=
    Term.func .add [Term.var "x", Term.var "y"]

#eval @Term.eval ex_sig_peano String ℕ ex_interpret_peano ex_assig_peano ex_term_peano

lemma ex_peano_proof: @Formula.eval ex_sig_peano String ℕ instDecidableEqString
    ex_interpret_peano ex_assig_peano ex_formula_peano := by
  simp
  intro a b
  apply Iff.intro
  · intro h
    cases h
    next h' =>
      use b - a
      refine Nat.add_sub_of_le ?_
      exact h'.le
    · use 0; assumption
  · intro h
    obtain ⟨z, hz⟩ := h
    cases hz
    simp only [Nat.lt_add_right_iff_pos, Nat.self_eq_add_right]
    exact Or.symm (Nat.eq_zero_or_pos z)

def exa : Formula ex_sig_peano String := .and .falsum .verum
example : ¬@Formula.eval ex_sig_peano _ _ _ ex_interpret_peano ex_assig_peano exa :=
  of_eq_true (Eq.trans (congrArg Not (and_true False)) not_false_eq_true)

example : @EntailsInterpret ex_sig_peano String _ _ ex_interpret_peano
  ex_assig_peano ex_formula_peano := ex_peano_proof


variable {sig : Signature} {X : Variables} {univ : Universes}
/-
Proposition 3.3.3 Let F and G be formulas, let N be a set of formulas. Then
(i) F is valid if and only if ¬F is unsatisfiable.
(ii) F |= G if and only if F ∧ ¬G is unsatisfiable.
(iii) N |= G if and only if N ∪ {¬G} is unsatisfiable.
-/
theorem valid_iff_not_unsat' [inst : DecidableEq X] (F : Formula sig X) :
    @Valid _ _ univ _ F ↔ @Unsatisfiable _ _ univ _ (Formula.neg F) := by simp

theorem entails_iff_and_not_unsat' [inst : DecidableEq X] (F G : Formula sig X) :
    @Entails _ _ univ _ F G ↔ @Unsatisfiable _ _ univ _ (Formula.and F (Formula.neg G)) := by simp

theorem setEntails_iff_union_not_unsat' [inst : DecidableEq X]
    (N : Set $ Formula sig X) (G : Formula sig X) :
    @SetEntails _ _ univ _ N G ↔ @SetUnsatisfiable _ _ univ _ (N ∪ {Formula.neg G}) := by
  apply Iff.intro
  · intro hentails I β
    simp_all only [SetEntails, Assignment, EntailsInterpret, Set.union_singleton,
      Set.mem_insert_iff, exists_eq_or_imp, Formula.eval, not_not]
    specialize hentails I β
    generalize Formula.eval I β G = pro at *
    by_cases halltrue : ∀ G ∈ N, Formula.eval I β G <;> aesop
  · intro hunsat
    intro I β hgstrue
    specialize hunsat I β
    aesop


/- ## Exercise 4 -/

namespace Exercise4

/- ### Exercise 4-1 -/

inductive fs where | b | c | d | f deriving BEq
inductive ps where | P
def F : Formula ⟨fs, ps⟩ String := .and (.and (.and (.atom (.pred .P [.func .b []]))
  (.atom (.pred .P [.func .c []])))
  (.neg (.atom (.pred .P [.func .d []]))))
  (.neg (.ex "x" (.atom (.pred .P [.func .f [.func .f [.var "x"]]]))))

theorem ex_4_1 : ∃ I : Interpretation ⟨fs, ps⟩ (Fin 2), ∃ β : Assignment String (Fin 2),
    Formula.eval I β F := by
  let I : Interpretation ⟨fs, ps⟩ (Fin 2) := ⟨
    fun g a => if g == .f || g == .d then 1 else 0,
    fun _ u => if u[0]! == 0 then True else False⟩
  use I
  use (fun _ => 0)
  simp [I, F]
  have : fs.f == fs.f := rfl
  aesop


/-
Exercise 4.7 (*)
Let Π be a set of propositional variables. Let N and N' be sets
of clauses over Π. Let S be a set of literals that does not contain any complementary
literals. Prove: If every clause in N contains at least one literal L with L ∈ S and if no
clause in N' contains a literal L with L ∈ S, then N ∪ N' is satisfiable if and only if N'
is satisfiable.
-/
def Interpretation.add (I : Interpretation ⟨Empty, String⟩ String)
    (β : Assignment Empty String) (L : Literal ⟨Empty, String⟩ Empty) :
    Interpretation ⟨Empty, String⟩ String :=
  -- add something to I such that Formula.eval L is true
  Interpretation.mk I.functions (match L with
    | Literal.pos a => match a with
      | Atom.pred p args =>
        have argsinter := args.map (Term.eval I β)
        (fun p' args' => if p' == p && args' == argsinter
          then True
          else I.predicates p' args')
    | Literal.neg a => match a with
      | Atom.pred p args =>
        have argsinter := args.map (Term.eval I β)
        (fun p' args' => if p' == p && args' == argsinter
          then False
          else I.predicates p' args')
  )

lemma tmp (I : Interpretation ⟨Empty, String⟩ String) (β : Assignment Empty String)
    (C : Clause ⟨Empty, String⟩ Empty)
    (hCsat : EntailsInterpret I β C) (L : Literal ⟨Empty, String⟩ Empty) (h : L.comp ∉ C) :
    EntailsInterpret (Interpretation.add I β L) β C := by
  sorry

theorem ex_4_7
    (N N' : Set <| Clause ⟨Empty, String⟩ Empty) (S : Set <| Literal ⟨Empty, String⟩ Empty)
    (hSnoCompl : ∀ L ∈ S, L.comp ∉ S)
    (hNsatByS : ∀ C ∈ N, ∃ L ∈ C, L ∈ S) (hN'noComplS : ∀ C ∈ N', ¬∃ L ∈ C, L.comp ∈ S) :
    (@ClauseSetSatisfiable _ _ univ _ (N ∪ N') ↔ @ClauseSetSatisfiable _ _ univ _ N') := by
  simp only [not_exists, not_and] at hN'noComplS
  apply Iff.intro
  · simp [ClauseSetSatisfiable]
    intro I β h
    apply Exists.intro
    · apply Exists.intro
      · intro C a
        apply h
        simp_all only [or_true]
  · simp [ClauseSetSatisfiable]
    intro I_N' β_N' hN'sat
    use I_N'
    use β_N' -- delay instanciation of assignment
    intro C hC
    cases hC
    next hCinN =>
      /- This is the actual hard case of this exercise. On paper it might look like this:
          - Show that I_N' and β_N' do not contradict (SAT N) (this is due to hN'noComplS)
          - Expand β_N' by the assignments implied by S to β_N'andS
          - then β_N'andS satisfies N using hNsatByS
      -/
      obtain ⟨L, ⟨hLinC, hLinS⟩⟩ := hNsatByS C hCinN
      have hLcompninS : L.comp ∉ S := by exact hSnoCompl L hLinS
      --let ?β := β_N'
      --let β_N'andS := β.modify L
      sorry

    next hCinN' => exact hN'sat C hCinN'

end Exercise4
