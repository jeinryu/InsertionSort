import InsertionSort.Spec
import InsertionSort.InductiveProof

-- insrt operation preserves permutation property
theorem insrt_Perm (x : Nat) (l : List Nat) :
List.Perm (x :: l) (insrt x l) := by
  induction l with
  | nil => simp [insrt]
  | cons h t ih =>
    by_cases h₁ : x ≤ h <;> simp [insrt, h₁]
    . have h₂ : (h :: x :: t).Perm (h :: insrt x t) := by simp; exact ih
      have h₃ : (x :: h :: t).Perm (h :: x :: t) := by apply List.Perm.swap
      apply List.Perm.trans h₃ h₂

-- sort algorithm satisfies permutation property
theorem sort_Perm (l : List Nat) : l.Perm (sort l) := by
  induction l with
  | nil => simp; rfl
  | cons h t ih =>
      simp [sort]
      have h₁ : (h :: t).Perm (h :: sort t) := by simp; exact ih
      have h₂ : (h :: sort t).Perm (insrt h (sort t)) := by apply insrt_Perm
      apply List.Perm.trans h₁ h₂

theorem insertion_sort_correct: is_sorting sort := by
  intro l
  constructor
  . -- Sortedness
    exact sort_Sorted l
  . -- Permutation
    exact sort_Perm l
