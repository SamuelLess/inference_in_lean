import InferenceInLean.Syntax

set_option autoImplicit false
--set_option diagnostics true

open Syntax
namespace Semantics

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

-- β[x1 ↦ β(x1), ..., xn ↦ β(xn)] = β
@[simp]
def Assignment.modify_rfl {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (x : X) : β.modify x (β x) = β := by
  funext y
  rw [Assignment.modify]
  split_ifs with heq
  · rw [heq]
  · rfl

-- x ≠ y → β[x ↦ a, y ↦ b] = β[y ↦ b, x ↦ a]
@[simp]
def Assignment.modify_comm {X : Variables} {univ : Universes} [DecidableEq X]
    {β : Assignment X univ} (x y : X) (a b : univ) :
    x ≠ y → (β.modify x a).modify y b = (β.modify y b).modify x a := by
  aesop

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

-- β[x1 ↦ a1, ..., xn ↦ an]
@[simp]
def Assignment.bigModify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) :
    Assignment X univ :=
  match xs, as with
  | x :: xs, a :: as => Assignment.bigModify (β.modify x a) xs as
  | _, _ => β

-- β[] = β
@[simp]
lemma Assignment.bigModify_empty {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) : β.bigModify [] [] = β := rfl

-- β[x ↦ a, x1 ↦ a1, ..., xn ↦ xn] (x) = a
@[simp]
lemma Assignment.bigModify_single_eq {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (huniq : xs.Nodup) (as : List univ)
    (hlen : xs.length = as.length) (x : X) (a : univ) (hx : x ∉ xs) :
    (β.modify x a).bigModify xs as x = a := by
  induction' xs with y xs ih generalizing β as x a
  · simp_all only [List.nodup_nil, List.length_nil, bigModify, modify, ↓reduceIte]
  · match as with
    | [] => simp_all only [Assignment, List.nodup_cons, List.length_cons,
      List.length_nil, Nat.add_one_ne_zero]
    | b :: as =>
      rw [Assignment.bigModify]
      rw [Assignment.modify_comm x y a b (List.ne_of_not_mem_cons hx)]
      exact ih (β.modify y b) (List.Nodup.of_cons huniq) as
        (Nat.succ_inj'.mp hlen) x a (by exact List.not_mem_of_not_mem_cons hx)

-- y ∉ [x1, ..., xn] → β[x1 ↦ a1, ..., xn ↦ an] y = β y
@[simp]
lemma Assignment.bigModify_nonmem {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (y : X) (hnonmem : y ∉ xs)
    (as : List univ) (hlen : xs.length = as.length) :
    β.bigModify xs as y = β y := by
  induction' xs with x xs ih generalizing as β
  · rw [Assignment.bigModify]
    aesop
  · match as with
    | [] => simp_all only [List.mem_cons, not_or, List.length_cons, List.length_nil,
      Nat.add_one_ne_zero]
    | a :: as =>
      rw [Assignment.bigModify]
      simp_all only [List.length_cons, Nat.add_right_cancel_iff, modify, ↓reduceIte]
      specialize ih (β.modify x a) (List.not_mem_of_not_mem_cons hnonmem) as rfl
      rw [ih]
      simp_all only [List.mem_cons, not_or, modify, ↓reduceIte]

set_option linter.unusedVariables false
-- surjectivity: ∀ a ∈ [a1, ..., an], ∃ x ∈ [x1, ..., xn], β[a₁, ..., an] (x) = a
lemma Assignment.bigModify_sur {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (huniq : xs.Nodup) (as : List univ)
    (a : univ) (ha : a ∈ as) (hlen : xs.length = as.length) :
    ∃ (x : X) (hx : x ∈ xs), β.bigModify xs as x = a := by
  induction' xs with x xs ih generalizing β as
  · match as with
    | [] => simp_all only [List.nodup_nil, List.not_mem_nil]
    | a' :: as' => simp_all only [List.nodup_nil, List.mem_cons, List.length_nil,
      List.length_cons, Nat.self_eq_add_left, Nat.add_one_ne_zero]
  · match as with
    | [] => simp_all only [Assignment, exists_prop, List.nodup_cons, List.not_mem_nil]
    | a' :: as' =>
      rw [Assignment.bigModify]
      apply List.mem_cons.mp at ha
      rcases ha with hfirst | has'
      · use x
        use (List.mem_cons_self x xs)
        rw [← hfirst]
        exact bigModify_single_eq
          β xs (List.Nodup.of_cons huniq) as' (Nat.succ_inj'.mp hlen) x a (List.Nodup.not_mem huniq)
      · specialize ih (β.modify x a') (List.Nodup.of_cons huniq) as' (has') (Nat.succ_inj'.mp hlen)
        rcases ih with ⟨x', ⟨hxinbounds, h⟩⟩
        use x'
        use (List.mem_cons_of_mem x hxinbounds)
set_option linter.unusedVariables true

lemma List.nodup_index_unique {α} [DecidableEq α] {l : List α} {a : α}
    (ha : a ∈ l) (huniq : l.Nodup) :
    ∃ (i : ℕ) (hinbounds : i < l.length),
      l[i] = a ∧
      l[l.indexOf a]'(List.indexOf_lt_length.mpr ha) = a ∧
      ∀ (j : ℕ) (hjinbounds : j < l.length), l[j] = a → i = j := by
  have h := List.mem_iff_getElem.mp ha
  rcases h with ⟨i, ⟨hinbounds, hmem⟩⟩
  use i
  use hinbounds
  subst hmem
  simp_all only [ne_eq, List.getElem_mem, true_and]
  split_ands
  · exact List.getElem_indexOf (List.indexOf_lt_length.mpr ha)
  · intro j hjinbounds heq
    exact (List.Nodup.getElem_inj_iff huniq).mp (id (Eq.symm heq))

-- β[x1 ↦ a1, ..., xi ↦ ai, ..., xn ↦ an] (xi) = ai
@[simp]
lemma Assignment.bigModify_single_index {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (huniq : xs.Nodup) (as : List univ)
    (n : ℕ) (hn : n = xs.length) (hnempty : xs ≠ []) (hlen : xs.length = as.length)
    (i : ℕ) (hiinbounds : i < xs.length) :
    β.bigModify xs as xs[i] = as[i] := by
  induction' n using Nat.strong_induction_on with n ih generalizing β xs as i
  by_cases hnleone : n ≤ 1
  · by_cases hnzero : n = 0
    · have h : xs = [] := by rw [hnzero] at hn; exact List.length_eq_zero.mp (id (Eq.symm hn))
      exact False.elim (hnempty h)
    · simp at hnzero
      have hi : i = 0 := by omega
      subst i
      match xs, as with
      | x :: xs, a :: as =>
        have hlen : xs.length = as.length := Nat.succ_inj'.mp hlen
        have hxs : xs.length = 0 := by
          clear ih huniq hnempty hiinbounds
          simp_all only [List.length_cons, Nat.reduceLeDiff, Nat.le_zero_eq, List.length_eq_zero,
            List.length_singleton, Nat.succ_ne_self, not_false_eq_true, List.length_nil]
        have has : as.length = 0 := by rw [hlen] at hxs; exact hxs
        have hxempty : xs = [] := by exact List.length_eq_zero.mp hxs
        have haempty : as = [] := by exact List.length_eq_zero.mp has
        simp only [hxempty, haempty, bigModify, modify, List.getElem_cons_zero, ↓reduceIte]
      | [], [] => simp_all only [List.nodup_nil, ne_eq, not_true_eq_false]
  · apply not_le.mp at hnleone
    match xs, as with
    | x :: xs, a :: as =>
      induction' i with i ih'
      · clear ih
        simp_all only [List.nodup_cons, ne_eq, reduceCtorEq, not_false_eq_true, List.length_cons,
          Nat.lt_add_left_iff_pos, bigModify, List.getElem_cons_zero]
        simp_all only [List.length_cons, Nat.add_right_cancel_iff, Nat.zero_lt_succ,
          not_false_eq_true, bigModify_nonmem, modify, ↓reduceIte]
      · clear ih'
        rw [bigModify]
        have hxsnonempty : xs ≠ [] := by
          have h : 1 < (x :: xs).length := by exact Nat.lt_of_lt_of_eq hnleone hn
          have h2 : 0 < xs.length := by exact Nat.lt_add_left_iff_pos.mp h
          exact List.ne_nil_of_length_pos h2
        specialize ih (n - 1) (Nat.sub_one_lt_of_lt hnleone) (β.modify x a) xs
          (List.Nodup.of_cons huniq) as (Eq.symm (Nat.eq_sub_of_add_eq (id (Eq.symm hn))))
          (hxsnonempty) (Nat.succ_inj'.mp hlen) i (Nat.succ_lt_succ_iff.mp hiinbounds)
        subst hn
        simp_all only [List.nodup_cons, ne_eq, reduceCtorEq, not_false_eq_true, List.length_cons,
          Nat.lt_add_left_iff_pos, bigModify, List.getElem_cons_succ]
    | [], [] => simp_all only [List.nodup_nil, ne_eq, not_true_eq_false]

lemma Assignment.bigModify_getIndex {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (y : X) (hmem : y ∈ xs) (hnempty : xs ≠ [])
    (as : List univ) (hlen : xs.length = as.length) (huniq : xs.Nodup) :
    ∃ (i : ℕ) (hiinbounds : i < xs.length),
      xs[i] = y ∧ β.bigModify xs as y = as[i] := by
  have hexists := List.mem_iff_getElem.mp hmem
  rcases hexists with ⟨i, ⟨hiinbounds, heq⟩⟩
  use i
  use hiinbounds
  subst heq
  simp_all only [List.getElem_mem, true_and]
  exact bigModify_single_index β xs huniq as as.length (Eq.symm hlen) hnempty hlen i hiinbounds

lemma Assignment.bigModify_mem {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (n : ℕ) (hn : n = xs.length) (hnempty : xs ≠ [])
    (as : List univ) (hlen : xs.length = as.length) (huniq : xs.Nodup) :
    ∀ (x : X) (hmem : x ∈ xs),
      β.bigModify xs as x = as[List.indexOf x xs]'(by
        rw [← hlen]
        exact List.indexOf_lt_length.mpr hmem
      ) := by
  intro y hmem
  have hindex := List.nodup_index_unique hmem huniq
  rcases hindex with ⟨i, hinbounds, heq, hindexOf, hiuniq⟩
  have h : List.indexOf xs[i] xs = i := by exact List.indexOf_getElem huniq i hinbounds
  simp only [← heq, h]
  exact bigModify_single_index β xs huniq as n hn hnempty hlen i hinbounds

-- An alternative way to formalize expressions of the form β[x1 ↦ a1, ..., xn ↦ an]
@[simp]
def Assignment.modFn {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) (hlen : xs.length = as.length) :
    Assignment X univ :=
  fun x ↦ if hmem : x ∈ xs then by
    exact as[xs.indexOf x]'(by rw [← hlen]; exact List.indexOf_lt_length.mpr hmem)
  else β x

@[simp]
lemma Assignment.modFn_empty {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) :
    β.modFn [] [] rfl = β := rfl

@[simp]
lemma Assignment.modFn_single {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (x : X) (a : univ) :
    β.modFn [x] [a] rfl = β.modify x a := by aesop

-- Proof that both assignment definitions are equal
lemma Assignment.bigModify_eq_modFn {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) (hnempty : xs ≠ [])
    (hlen : xs.length = as.length) (huniq : xs.Nodup) :
    β.bigModify xs as = β.modFn xs as hlen := by
  funext y
  rw [Assignment.modFn]
  split_ifs with hmem
  · exact Assignment.bigModify_mem β xs as.length (id (Eq.symm hlen)) hnempty as hlen huniq y hmem
  · exact Assignment.bigModify_nonmem β xs y hmem as hlen

/-
### Lemma 3.3.7
-/
-- β [x1 ↦ β(x1), ..., xn ↦ β(xn)] = β
lemma Assignment.substitute_equality {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) :
    β = Assignment.bigModify β xs (xs.map β) := by
  induction' xs with x xs ih
  · simp_all only [Assignment, Assignment.bigModify]
  · rw [List.map, Assignment.bigModify, β.modify_rfl]
    exact ih

lemma Assignment.modFn_eq_id {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ)
    (hlen : xs.length = as.length) (huniq : xs.Nodup) :
    xs.map (Assignment.modFn β xs as hlen) = as := by
  apply List.map_eq_iff.mpr
  intro i
  by_cases hin : i < as.length
  · simp_all [↓reduceDIte]
    have h : List.indexOf xs[i] xs = i := by apply List.get_indexOf huniq
    simp_all only
  · have hasnone : as[i]? = none := getElem?_neg as i hin
    have hxsnone : xs[i]? = none := by simp_all only [not_lt, getElem?_eq_none]
    rw [hasnone, hxsnone, Option.map]
