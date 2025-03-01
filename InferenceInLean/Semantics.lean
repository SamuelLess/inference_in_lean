import InferenceInLean.Syntax

set_option autoImplicit false
--set_option diagnostics true

open Syntax

/- ## 3.2 Semantics
Here, the syntatic definitions are expanded upon with semantic interpretations.  -/

namespace Semantics

def Universes := Type

variable (sig : Signature) (X : Variables) (univ : Universes)

/- A = (UA, (fA : UA n → UA)_f/n∈Ω, (PA ⊆ UA^m)P/m∈Π) -/
structure Interpretation where
  functions : sig.funs -> (List univ -> univ)
  predicates : sig.preds -> (List univ -> Prop)

@[simp]
def HerbrandInterpretation (sig : Signature) (preds : sig.preds -> List (Term sig Empty) -> Prop) :
    Interpretation sig (Term sig Empty) := ⟨fun f args => Term.func f args, preds⟩

/- ### Assigments
> β : X → univ
-/

@[simp]
def Assignment := X → univ

@[simp]
def Assignment.modify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (x : X) (a : univ) : Assignment X univ :=
  fun y => if y = x then a else β y

-- β[x1 ↦ β(x1), ..., xn ↦ β(xn)] = β
@[simp]
lemma Assignment.modify_rfl [DecidableEq X]
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
def Term.eval {sig : Signature} {X : Variables} {univ : Universes}
    (I : Interpretation sig univ) (β : Assignment X univ) : Term sig X -> univ
  | Term.var x => β x
  | Term.func f args => (I.functions f) <| args.attach.map (fun ⟨a, _⟩ => Term.eval I β a)

@[simp]
def Atom.eval {sig : Signature} {X : Variables} {univ : Universes}
    (I : Interpretation sig univ) (β : Assignment X univ) : Atom sig X -> Prop
  | Atom.pred p args => (I.predicates p) (args.map (Term.eval I β))

@[simp]
def Formula.eval {sig : Signature} {X : Variables} {univ : Universes} [DecidableEq X]
    (I : Interpretation sig univ) (β : Assignment X univ) : Formula sig X -> Prop
  | Formula.falsum => False
  | Formula.verum => True
  | Formula.atom a => Atom.eval I β a
  | Formula.neg f => ¬ Formula.eval I β f
  | Formula.and f g => Formula.eval I β f ∧ Formula.eval I β g
  | Formula.or f g => Formula.eval I β f ∨ Formula.eval I β g
  | Formula.imp f g => Formula.eval I β f → Formula.eval I β g
  | Formula.iff f g => Formula.eval I β f ↔ Formula.eval I β g
  | Formula.all x f => ∀ a : univ, Formula.eval I (β.modify x a) f
  | Formula.ex x f => ∃ a : univ, Formula.eval I (β.modify x a) f

@[simp]
lemma Term.eval_without_free_not_term {sig : Signature} {X : Variables} [DecidableEq X]
    (t : Term sig X) : t.freeVars = {} → ¬∃ (x : X), t = Term.var x := by
  intro a
  simp_all only [not_exists]
  intro x
  apply Aesop.BuiltinRules.not_intro
  intro a_1
  subst a_1
  simp_all only [Term.freeVars.eq_1, Set.singleton_ne_empty]

lemma Set.singleton_of_union_empty {α : Type} {x : α} {A B : Set α}
    (h : ¬A = {x}) (hsingleton : A ∪ B = {x}) : A = ∅ := by
  have sub : A ⊆ {x} := by
    rw [← hsingleton]
    exact Set.subset_union_left
  have : A = ∅ ∨ A = {x} := by
    exact Set.subset_singleton_iff_eq.mp sub
  simp_all only [Set.subset_singleton_iff, or_false]

@[simp]
lemma Term.subterms_closed {sig : Signature} {X : Variables} {_I : Interpretation sig univ}
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
lemma Term.one_freeVar_of_subterms {univ : Universes} {sig : Signature} {X : Variables}
    (_I : Interpretation sig univ) [DecidableEq X] {t : Term sig X} {x : X} :
    ∀ (f : sig.funs) (args : List (Term sig X)), t = Term.func f args →
    t.freeVars = {x} →
    ∀ (arg : Term sig X) (_harg : arg ∈ args), arg.freeVars = {x} ∨ arg.freeVars = {} := by
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

@[simp]
lemma Assignment.eval_closed_term {sig : Signature} {X : Variables} {I : Interpretation sig univ}
    [DecidableEq X] (t : Term sig X)
    (x : X) : t.freeVars = {} → ∀ (β γ : Assignment X univ) (_a : univ),
      Term.eval I β t = Term.eval I γ t := by
  intro hclosed β γ a
  induction' t using Term.induction with y args ih f generalizing β γ a
  · simp_all only [Term.freeVars.eq_1, Set.singleton_ne_empty]
  · simp_all only [Assignment, Term.eval, List.map_subtype, List.unattach_attach]
    have hargsareequal : List.map (Term.eval I β) args =
        List.map (Term.eval I γ) args := by
      simp_all only [List.map_inj_left]
      intro arg harg
      have s := @Term.subterms_closed univ sig X I _ (Term.func f args) x f args rfl hclosed arg harg
      specialize ih arg harg s β γ a
      rw [ih]
    rw [← hargsareequal]

#check Term.subterms_closed

@[simp]
lemma Assignment.eval_term_with_one_free {univ : Universes} {sig : Signature} {X : Variables}
    {I : Interpretation sig univ} [DecidableEq X] {t : Term sig X}
    {x : X} : t.freeVars = {x} → ∀ (β γ : Assignment X univ) (a : univ),
      Term.eval I (β.modify x a) t = Term.eval I (γ.modify x a) t := by
  intro honefree β γ a
  induction' t using Term.induction with y args ih f
  · simp_all only [Term.freeVars.eq_1, Set.singleton_eq_singleton_iff, Term.eval, modify,
      ↓reduceIte]
  · simp_all only [Term.eval, List.map_subtype, List.unattach_attach]
    have hargsareequal :
        List.map (Term.eval I (β.modify x a)) args = List.map (Term.eval I (γ.modify x a)) args := by
      simp_all only [List.map_inj_left]
      intro arg harg
      have honeornone := Term.one_freeVar_of_subterms I f args rfl honefree arg harg
      rcases honeornone with hone | hnone
      · aesop
      · apply Assignment.eval_closed_term
        · exact x
        · simp_all only
        · exact a
    rw [hargsareequal]

/- @[simp]
def Term.eval_without_free {sig : Signature} {X : Variables} [DecidableEq X] (t : Term sig X) :
    t.freeVars = {} → ∀ (f : sig.funs) (args : List (Term sig X)),
      t = Term.func f args → args = [] := by
  intro hclosed f args heq
  by_contra harg
  induction' t using Term.induction with x args ih f generalizing args
  · sorry
  ·
    simp_all only [imp_false, not_not, Term.func.injEq]
    obtain ⟨left, right⟩ := heq
    subst left right
    apply harg
    have hex : ∃ (t : Term sig X), t ∈ args := List.exists_mem_of_ne_nil args harg
    rcases hex with ⟨arg, harg⟩
    specialize ih (Term.func f args)
    have h : ∀ term ∈ args,
      Term.freeVars sig X term = ∅ → ∀ (args : List (Term sig X)), term = Term.func f args := sorry
    specialize ih h -/


lemma List.reduce_to_empty {α β: Type} {xs : List α} {as : List β}
    (hlen : xs.length = as.length) (hzero : as.length = 0 ∨ xs.length = 0) : xs = [] ∧ as = [] := by
  simp_all only [List.length_eq_zero, or_self, and_true, List.length_nil]
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

lemma Assignment.bigModify_append {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) (n : ℕ) (hn : n = xs.length)
    (hlen : xs.length = as.length) (y : X) (b : univ) (hy : y ∉ xs) :
    β.bigModify (xs ++ [y]) (as ++ [b]) = (β.bigModify xs as).modify y b := by
  induction' n with n ih generalizing β xs as
  · obtain ⟨hxsempty, hasempty⟩ := List.reduce_to_empty hlen (by simp_all only [or_self])
    subst hxsempty hasempty
    simp only [Assignment, List.nil_append, bigModify]
  · match xs, as with
    | x :: xs, a :: as =>
      specialize ih (β.modify x a) xs as
        (by simp_all only [List.length_cons, Nat.add_right_cancel_iff])
        (Nat.succ_inj'.mp hlen) (List.not_mem_of_not_mem_cons hy)
      rw [bigModify, List.cons_append, List.cons_append, bigModify]
      rw [ih]
    | [], [] => rfl

@[simp]
lemma Assignment.bigModify_modify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) (y : X) (b : univ) (hxuniq : xs.Nodup)
    (hxnotinxs : y ∉ xs) (n : ℕ) (hn : n = xs.length) (hlen : xs.length = as.length) :
    (β.bigModify xs as).modify y b = (β.modify y b).bigModify xs as := by
  induction' n with n ih generalizing xs as β
  · obtain ⟨hxsempty, hasempty⟩ := List.reduce_to_empty hlen (by simp_all only [or_self])
    subst hxsempty hasempty
    simp_all only [List.nodup_nil, List.not_mem_nil, not_false_eq_true, List.length_nil, Assignment,
      bigModify]
  · match xs, as with
    | x :: xs, a :: as =>
      rw [bigModify, bigModify]
      specialize ih (β.modify x a) xs as (List.Nodup.of_cons hxuniq)
        (List.not_mem_of_not_mem_cons hxnotinxs)
        (by simp_all only [Assignment, List.nodup_cons, List.mem_cons, not_or, List.length_cons,
          Nat.add_right_cancel_iff])
        (by exact Nat.succ_inj'.mp hlen)
      rw [ih, modify_comm x y a b (Ne.symm (List.ne_of_not_mem_cons hxnotinxs))]
    | [], [] =>
      simp_all only [List.nodup_nil, List.not_mem_nil, not_false_eq_true, List.length_nil,
        bigModify, implies_true, Nat.add_one_ne_zero]

@[simp]
lemma Assignment.bigModify_add_nondup {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (as : List univ) (x : X) (a : univ) :
    ((β.bigModify xs as).modify x a) x = a := by
  simp_all only [modify, ↓reduceIte]

#check List.drop
/- lemma Assignment.bigModify_nodup_erase {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (_huniq : xs.Nodup) (as : List univ)
    (_hlen : xs.length = as.length) (x : X) (a : univ) (_hx : x ∈ xs)
    (i : ℕ) (hiinbounds : i < xs.length) (hi : xs[i] = x) (ha : as[i] = a) :
    ∀ (y : X), β.bigModify (xs.eraseIdx i) (as.eraseIdx i) y = if x == y then β x -/
#check List.Nodup.erase
/- lemma Assignment.bigModify_add_nondup {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (_huniq : xs.Nodup) (as : List univ)
    (_hlen : xs.length = as.length) (x : X) (a : univ) (_hx : x ∈ xs) :
    (i : ℕ) (hi : xs[i] = x) (a' : univ) (ha : as[i] = a')
    (bigModify (xs.dropIdx i) (as.dropIdx i)).modify x a = β := by sorry -/

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

-- surjectivity: ∀ a ∈ [a1, ..., an], ∃ x ∈ [x1, ..., xn], β[a₁, ..., an] (x) = a
lemma Assignment.bigModify_sur {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (huniq : xs.Nodup) (as : List univ)
    (a : univ) (ha : a ∈ as) (hlen : xs.length = as.length) :
    ∃ (x : X) (_hx : x ∈ xs), β.bigModify xs as x = a := by
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

lemma Assignment.bigModify_erase_modify_eq_modify {X : Variables} {univ : Universes} [DecidableEq X]
    (β : Assignment X univ) (xs : List X) (n : ℕ) (hn : n = xs.length) (hnempty : xs ≠ [])
    (as : List univ) (hlen : xs.length = as.length) (huniq : xs.Nodup) :
    ∀ (y : X) (b : univ) (i : ℕ) (hiinbounds : i < n) (hiindex : xs[i] = y ∧ as[i] = b),
    β.bigModify (xs.eraseIdx i ++ [y]) (as.eraseIdx i ++ [b]) = (β.bigModify xs as).modify y b := by
  intro x a i hiinbounds hiindix
  wlog hlast : i = n - 1
  · sorry
  ·
    subst hlast
    simp_all only [ne_eq, Assignment, List.eraseIdx_length_sub_one]
    obtain ⟨left, right⟩ := hiindix
    subst right left
    induction' n with n ih generalizing xs as
    · sorry
    · match xs, as with
      | x :: xs, a :: as =>
        simp_all only [reduceCtorEq, not_false_eq_true, List.nodup_cons, List.length_cons, Nat.add_one_sub_one,
          bigModify]
        obtain ⟨hnonmem, hxuniq⟩ := huniq
        sorry
      | [], [] => simp_all only [not_true_eq_false]

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

lemma Term.eval_of_many_free {univ : Universes} {sig : Signature} {X : Variables}
    [inst : DecidableEq X] (I : Interpretation sig univ) (T : Term sig X) (xs : List X)
    (as : List univ) (hxuniq : xs.Nodup) (hlen : xs.length = as.length) (n : ℕ) (hn : n = xs.length)
    (hfree : T.freeVars ⊆ xs.toFinset) : (∀ (β γ : Assignment X univ),
      Term.eval I (β.bigModify xs as) T = Term.eval I (γ.bigModify xs as) T) := by
  simp_all only [List.coe_toFinset]
  induction' T using Term.induction with y args ih f
  · simp_all only [Term.freeVars.eq_1, Set.singleton_subset_iff, Set.mem_setOf_eq, eval]
    induction' n with n ih generalizing xs as
    · obtain ⟨hxsempty, hasempty⟩ := List.reduce_to_empty hlen (by simp_all only [or_self])
      subst hasempty hxsempty
      simp_all only [List.length_nil, List.nodup_nil, List.not_mem_nil]
    · match xs, as with
      | x :: xs, a :: as =>
        intro β γ
        simp_all only [Assignment, List.nodup_cons, List.length_cons, Nat.add_right_cancel_iff,
          List.mem_cons, Assignment.bigModify]
        subst hn
        obtain ⟨left, right⟩ := hxuniq
        cases hfree with
        | inl h =>
          subst h
          simp_all only [not_false_eq_true, Assignment.bigModify_nonmem, Assignment.modify,
            ↓reduceIte]
        | inr h_1 =>
          apply ih <;> simp_all only
      | [], [] => simp_all only [Assignment, List.nodup_nil, List.length_nil, Nat.add_one_ne_zero]
  · intro β γ
    subst hn
    simp_all only [Assignment, eval, List.map_subtype, List.unattach_attach]
    have hargsareequal : List.map (eval I (β.bigModify xs as)) args =
        List.map (eval I (γ.bigModify xs as)) args := by
      simp_all only [List.map_inj_left]
      intro arg harg
      have hsubset : Term.freeVars sig X arg ⊆ {a | a ∈ xs} := by
        have hsub := Term.arg_subset_of_freeVars args f arg harg
        exact fun ⦃a⦄ a_1 ↦ hfree (hsub a_1)
      specialize ih arg harg hsubset β γ
      exact ih
    rw [hargsareequal]

lemma Atom.eval_of_many_free {univ : Universes} {sig : Signature} {X : Variables}
    [inst : DecidableEq X] (I : Interpretation sig univ) (A : Atom sig X) (xs : List X)
    (as : List univ) (hxuniq : xs.Nodup) (hlen : xs.length = as.length) (n : ℕ)
    (_hn : n = xs.length) (hfree : A.freeVars ⊆ xs.toFinset) : (∀ (β γ : Assignment X univ),
      Atom.eval I (β.bigModify xs as) A = Atom.eval I (γ.bigModify xs as) A) := by
  induction' A with P args
  intro β γ
  simp_all only [Atom.freeVars, List.coe_toFinset, eval, eq_iff_iff]
  have hargsareequal : List.map (Term.eval I (β.bigModify xs as)) args =
      List.map (Term.eval I (γ.bigModify xs as)) args := by
    simp_all only [List.map_inj_left]
    intro arg harg
    have hsubset : Term.freeVars sig X arg ⊆ ↑xs.toFinset := by
      simp_all only [List.coe_toFinset]
      have hsub : Term.freeVars sig X arg ⊆ (Atom.pred P args).freeVars := by
        induction' args with arg' args ih
        · simp_all only [Atom.freeVars, Set.empty_subset, List.not_mem_nil]
        · simp_all only [Atom.freeVars, Set.union_subset_iff, List.mem_cons, forall_const]
          obtain ⟨left, right⟩ := hfree
          cases harg with
          | inl h =>
            subst h
            simp_all only [Set.subset_union_left]
          | inr h_1 =>
            simp_all only [forall_const]
            exact Set.subset_union_of_subset_right ih (Term.freeVars sig X arg')
      exact fun ⦃a⦄ a_1 ↦ hfree (hsub a_1)
    have heval := Term.eval_of_many_free I arg xs as hxuniq hlen xs.length rfl hsubset β γ
    exact heval
  rw [hargsareequal]

#check Term.freeVars
lemma Formula.eval_of_many_free {univ : Universes} {sig : Signature} {X : Variables}
    [inst : DecidableEq X] (I : Interpretation sig univ) (F : Formula sig X) (xs : List X)
    (as : List univ) (hxuniq : xs.Nodup) (hlen : xs.length = as.length)
    (hfree : F.freeVars ⊆ xs.toFinset) : (∀ (β γ : Assignment X univ),
      Formula.eval I (β.bigModify xs as) F = Formula.eval I (γ.bigModify xs as) F) := by
  intro β γ
  induction' F with a F ih F G ihF ihG F G ihF ihG F G ihF ihG F G ihF ihG y F ih y F ih generalizing β γ xs as
  · simp_all only [Formula.freeVars, eval]
  · simp_all only [Formula.freeVars, eval]
  · induction' a with p args
    have hatom := Atom.eval_of_many_free I (Atom.pred p args) xs as hxuniq hlen xs.length rfl
      (by simp_all only [Formula.freeVars, Atom.freeVars, List.coe_toFinset]) β γ
    simp_all only [Formula.freeVars, Atom.freeVars, List.coe_toFinset, Atom.eval, eq_iff_iff, eval]
  · rw [eval, eval]
    specialize ih xs as hxuniq hlen hfree β γ
    exact congrArg Not ih
  · rw [eval, eval]
    rw [Formula.freeVars] at hfree
    specialize ihF xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_left h)) β γ
    specialize ihG xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_right h)) β γ
    simp_all only [List.coe_toFinset, Set.union_subset_iff, eq_iff_iff]
  · rw [eval, eval]
    rw [Formula.freeVars] at hfree
    specialize ihF xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_left h)) β γ
    specialize ihG xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_right h)) β γ
    simp_all only [List.coe_toFinset, Set.union_subset_iff, eq_iff_iff]
  · rw [eval, eval]
    rw [Formula.freeVars] at hfree
    specialize ihF xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_left h)) β γ
    specialize ihG xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_right h)) β γ
    simp_all only [List.coe_toFinset, Set.union_subset_iff, eq_iff_iff]
  · rw [eval, eval]
    rw [Formula.freeVars] at hfree
    specialize ihF xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_left h)) β γ
    specialize ihG xs as hxuniq hlen (fun _ h ↦ hfree (Set.subset_union_right h)) β γ
    simp_all only [List.coe_toFinset, Set.union_subset_iff, eq_iff_iff]
  · simp_all only [Assignment, eq_iff_iff, Formula.freeVars, eval]
    apply Iff.intro
    · intro heval a
      specialize heval a
      by_cases hxinxs : y ∈ xs
      · have hsub : F.freeVars ⊆ ↑xs.toFinset := by
          simp_all only [List.coe_toFinset, Set.diff_singleton_subset_iff, Set.mem_setOf_eq,
          Set.insert_eq_of_mem]
        -- remove y from xs, then modify with y
        rcases List.nodup_index_unique hxinxs hxuniq with ⟨i, hiinbounds, hiindex, hiindexOf, _⟩
        specialize ih (xs.eraseIdx i ++ [y]) (as.eraseIdx i ++ [a]) sorry sorry sorry β γ
        --rw [Assignment.bigModify_append] at ih
        --rw [Assignment.bigModify] at ih
        sorry
      · by_cases hfin : y ∈ F.freeVars
        · have hfreevars : F.freeVars ⊆ ↑(y :: xs).toFinset := by
            simp_all only [List.coe_toFinset, Set.diff_singleton_subset_iff, List.toFinset_cons,
              Finset.coe_insert]
          specialize ih (y :: xs) (a :: as) (List.Nodup.cons hxinxs hxuniq)
            (Nat.succ_inj'.mpr hlen) hfreevars β γ
          rw [Assignment.bigModify, Assignment.bigModify] at ih
          rw [Assignment.bigModify_modify γ xs as y a hxuniq hxinxs xs.length rfl hlen]
          rw [← ih]
          rw [← Assignment.bigModify_modify β xs as y a hxuniq hxinxs xs.length rfl hlen]
          exact heval
        · have hfreevars : F.freeVars \ {y} = F.freeVars := by exact Set.diff_singleton_eq_self hfin
          rw [hfreevars] at hfree
          specialize ih xs as hxuniq hlen hfree (β.modify y a) (γ.modify y a)
          rw [Assignment.bigModify_modify γ xs as y a hxuniq hxinxs xs.length rfl hlen]
          apply ih.mp
          rw [← Assignment.bigModify_modify β xs as y a hxuniq hxinxs xs.length rfl hlen]
          exact heval
    · sorry -- completely analogous
  · sorry -- completely analogous to forall

lemma Formula.eval_of_closed {univ : Universes} {sig : Signature} {X : Variables}
    [inst : DecidableEq X] (I : Interpretation sig univ) (F : Formula sig X)
    (hclosed : Formula.closed F) :
    (∀ (β γ : Assignment X univ), Formula.eval I β F = Formula.eval I γ F) := by
  intro β γ
  have s := Formula.eval_of_many_free I F [] [] List.nodup_nil rfl (by aesop) β γ
  rw [Assignment.bigModify, Assignment.bigModify] at s
  exact s
  · aesop
  · aesop
