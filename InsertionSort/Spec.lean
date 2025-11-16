-- Definition
def insrt (n : Nat) (l : List Nat) : List Nat :=
  match l with
  | [] => [n]
  | h :: t => if n <= h then n :: l else h :: insrt n t

def sort (l : List Nat) : List Nat :=
  match l with
  | [] => []
  | h :: t => insrt h (sort t)

-- 1. Specification of Sortedness

-- (1) Inductive definition
inductive Sorted : List Nat → Prop
  | nil : Sorted []
  | singleton (n : Nat) : Sorted [n]
  | cons (n : Nat) (m : Nat) (l : List Nat) :
      n ≤ m → Sorted (m :: l) → Sorted (n :: m :: l)

-- (2) Definition by index
def Sorted' (l : List Nat) : Prop :=
  ∀ (i j : Nat) (iv jv : Nat),
    i ≤ j →
    l[i]? = some iv →
    l[j]? = some jv →
    iv ≤ jv

-- correctness of a sorting algorithm
def is_sorting (f : List Nat → List Nat) :=
  ∀ l, Sorted (f l) ∧ List.Perm l (f l)

-- 2. Specification of contents-preserving
-- Multiset definition & lemmas
namespace Multiset
def Multiset := Nat → Nat

def empty : Multiset :=
  fun _ => 0

def singleton (v : Nat) : Multiset :=
  fun x => if x = v then 1 else 0

def union (a b : Multiset) : Multiset :=
  fun x => a x + b x

theorem union_assoc (a b c : Multiset) : union a (union b c) = union (union a b) c := by unfold union; funext x; omega

theorem union_comm (a b : Multiset) : union a b = union b a := by unfold union; funext x; omega

theorem union_swap (a b c : Multiset) : union a (union b c) = union b (union a c) := by
  rw [union_comm, union_comm a c, union_assoc]

-- Specification using multiset
def contents (l : List Nat) : Multiset :=
  match l with
  | [] => empty
  | x :: xs => union (singleton x) (contents xs)
namespace Multiset
