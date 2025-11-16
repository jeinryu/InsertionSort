import InsertionSort.Spec
open Multiset

theorem insrt_Contents (a : Nat) (l : List Nat) : contents (insrt a l) = contents (a :: l) := by
  induction l with
  | nil => simp [insrt]
  | cons x xs ih =>
      simp [insrt]
      by_cases h : a ≤ x <;> simp [h] -- positive case: done
      -- negative case left; ¬ a ≤ x
      simp [contents, ih, union_swap]

theorem sort_Contents (l : List Nat) : contents l = contents (sort l) := by
  induction l with
  | nil => simp [contents, sort]
  | cons x xs ih => simp [sort, insrt_Contents, contents, ih]
