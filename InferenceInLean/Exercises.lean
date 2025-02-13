import InferenceInLean.Basic
import Mathlib.Data.Finset.Defs

open FirstOrder

/-
### Example Peano Arithmetic
-/

inductive PeanoFuns where
  | zero
  | succ
  | add
  | mul

inductive PeanoPreds where
  | less_than

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
      (.atom (.eq (.var "x") (.var "y"))))
    (.ex "z" (.atom (.eq (.func .add [.var "x", .var "z"]) (.var "y"))))

@[simp]
def ex_interpret_peano : Interpretation ex_sig_peano where
  univ := ℕ
  functions := λ
    | .zero => λ _ => 0
    | .succ => λ xs => xs[0]! + 1
    | .add => λ xs => xs[0]! + xs[1]!
    | .mul => λ xs => xs[0]! * xs[1]!
  predicates := λ f => match f with
    | .less_than => λ xs => xs[0]! < xs[1]!

def ex_assig_peano : Assignment String Nat
  | "x" => 0
  | "y" => 0
  | _ => 0

def example_substitution : Substitution ex_sig_peano String := λ x => match x with
  | "x" => Term.func .succ [Term.var "y"]
  | _ => Term.var x

def ex_formula_peano_lt : @Formula ex_sig_peano String :=
  .all "z" (.atom $ .pred .less_than [.var "x", .func .succ [.func .succ [.var "z"]]])

lemma ex_proof_lt : @Formula.eval ex_sig_peano String instDecidableEqString
    ex_interpret_peano ex_assig_peano ex_formula_peano_lt := by
  simp [ex_formula_peano_lt, ex_sig_peano, Interpretation, Assignment, ex_assig_peano]

noncomputable def ex_formula_peano_lt_subst : @Formula ex_sig_peano String :=
  ex_formula_peano_lt.substitute example_substitution

lemma ex_proof_lt_subst : @Formula.eval ex_sig_peano String instDecidableEqString
    ex_interpret_peano ex_assig_peano ex_formula_peano_lt_subst := by
  simp only [ex_sig_peano, ex_interpret_peano, ex_formula_peano_lt_subst]
  unfold example_substitution
  simp only [example_substitution, ex_sig_peano]
  rw [ex_formula_peano_lt]
  simp [Formula.substitute, ex_interpret_peano, ex_assig_peano]

#eval @Term.eval ex_sig_peano String ex_interpret_peano ex_assig_peano (Term.var "y")

def ex_term_peano : Term ex_sig_peano String :=
    Term.func .add [Term.var "x", Term.var "y"]

#eval @Term.eval ex_sig_peano String ex_interpret_peano ex_assig_peano ex_term_peano

lemma ex_peano_proof: @Formula.eval ex_sig_peano String instDecidableEqString
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
example : ¬@Formula.eval ex_sig_peano _ _ ex_interpret_peano ex_assig_peano exa :=
  of_eq_true (Eq.trans (congrArg Not (and_true False)) not_false_eq_true)


example : @EntailsInterpret ex_sig_peano String _ ex_interpret_peano
  ex_assig_peano ex_formula_peano := ex_peano_proof


/-
Proposition 3.3.3 Let F and G be formulas, let N be a set of formulas. Then
(i) F is valid if and only if ¬F is unsatisfiable.
(ii) F |= G if and only if F ∧ ¬G is unsatisfiable.
-/
theorem valid_iff_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F : Formula sig X) : Valid F ↔ @Unsatisfiable sig X inst (Formula.neg F) := by simp

theorem entails_iff_and_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (F G : Formula sig X) :
    Entails F G ↔ @Unsatisfiable sig X inst (Formula.and F (Formula.neg G)) := by simp

/-
-- TODO: finish this proof
(iii) N |= G if and only if N ∪ {¬G} is unsatisfiable.
-/
theorem setEntails_iff_union_not_unsat {sig : Signature} {X : Variables} [inst : DecidableEq X]
    (N : Set $ Formula sig X) (G : Formula sig X) :
    SetEntails N G ↔ @SetUnsatisfiable sig X inst (N ∪ {Formula.neg G}) := by
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


/-
Exercise 4.7 (*)
Let Π be a set of propositional variables. Let N and N' be sets
of clauses over Π. Let S be a set of literals that does not contain any complementary
literals. Prove: If every clause in N contains at least one literal L with L ∈ S and if no
clause in N' contains a literal L with L ∈ S, then N ∪ N' is satisfiable if and only if N'
is satisfiable.
-/
theorem ex_4_7 {sig : Signature} {X : Variables} [DecidableEq X]
    (N N' : Set $ Clause sig X) (S : Set $ Literal sig X)
    (hSnoCompl : ∀ L ∈ S, L.comp ∉ S)
    (hNsatByS : ∀ C ∈ N, ∃ L ∈ C, L ∈ S) (hN'noComplS : ∀ C ∈ N', ∀ L ∈ C, L ∉ S) :
    (ClauseSetSatisfiable (N ∪ N') ↔ ClauseSetSatisfiable N') := by
  apply Iff.intro
  · simp [ClauseSetSatisfiable]
    intro I β
    intro h
    apply Exists.intro
    · apply Exists.intro
      · intro C a
        apply h
        simp_all only [or_true]
  · simp [ClauseSetSatisfiable]
    intro I_N' β_N'
    intro hN'sat
    use I_N'
    use β_N'
    intro C hC
    cases hC
    /- This is the actual hard case of this exercise. On paper it might look like this:
        - Show that I_N' and β_N' do not contradict (SAT N) (this is due to hN'noComplS)
        - Expand β_N' by the assignments implied by S to β_N'andS
        - then β_N'andS satisfies N using hNsatByS
    -/
    next h => sorry
    next h => exact hN'sat C h


lemma test {M : Set ℕ} (h : ∀ a, a ∉ M): M = ∅ := by exact Set.eq_empty_of_forall_not_mem h
