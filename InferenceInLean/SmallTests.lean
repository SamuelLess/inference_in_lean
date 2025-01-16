
import Mathlib.Data.Set.Basic

set_option autoImplicit false
--set_option diagnostics true



inductive Tree (α : Type) where
  | node (val: α) (children : List (Tree α))

def example_tree := Tree.node 1 [Tree.node 2 [], Tree.node 3 [Tree.node 4 []]]

def max_of_list {α : Type} [LT α] [DecidableRel (λ (x y : α) => x > y)]  [Inhabited α] : List α → α
  | [] => default
  | x :: xs => List.foldl (fun x y => if x > y then x else y) x xs

/-def sum_of_list : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum_of_list (x::xs)
-/
/-def depth_of_tree {α : Type} : Tree α → Nat
  | Tree.node val [] => 1
  | Tree.node val children => 1 + max_of_list (List.map depth_of_tree children)
-/

mutual
    def sum_of_tree : Tree Nat → Nat
      | Tree.node val [] => val
      | Tree.node val children => val + sum_of_subtree children
    def sum_of_subtree : List (Tree Nat) → Nat
      | [] => 0
      | x :: xs => sum_of_tree x + sum_of_subtree xs
end

def test : sum_of_tree example_tree = 10 := rfl

structure FunctionSymbol where
    symb : String
    arity : ℕ


inductive MyTerm (Variable : Set ℕ) (signature : Set FunctionSymbol) where
    | var (x: Variable)
    | func (f: FunctionSymbol)
        (h : f ∈ signature)
        (args: List (MyTerm Variable signature))
