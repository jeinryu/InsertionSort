import InsertionSort.Spec

-- insrt operation preserves Sorted property
theorem insrt_Sorted (a : Nat) (l: List Nat) :
 Sorted l → Sorted (insrt a l) := by
  intro h
  induction h with
  | nil => -- goal : Sorted (insrt a [])
      simp [insrt, Sorted.singleton]
  | singleton m => -- goal : Sorted (insrt a [m])
      simp [insrt]
      by_cases h₁ : a ≤ m
      · -- Case: n ≤ m
        simp [h₁]
        apply Sorted.cons
        · exact h₁
        · exact Sorted.singleton m
      · -- Case: ¬(n ≤ m)
        simp [h₁]
        apply Sorted.cons
        · exact Nat.le_of_lt (Nat.lt_of_not_ge h₁)
        · exact Sorted.singleton a
  | cons x y l hxy hs1 hs2 => -- goal : Sorted (insrt a (x :: y :: l))
      by_cases h₁ : a ≤ x <;> simp [insrt, h₁]
      . -- Case : a ≤ x
        apply Sorted.cons
        . exact h₁
        . apply Sorted.cons
          exact hxy
          exact hs1
      . -- Case : ¬(a ≤ x)
        by_cases h₂ : a ≤ y <;> simp [h₂]
        . -- Case : a ≤ y
          apply Sorted.cons
          omega
          apply Sorted.cons
          exact h₂
          exact hs1
        . apply Sorted.cons
          . exact hxy
          . simp [insrt, h₂] at hs2
            exact hs2

-- sort algorithm satisfies Sorted property
theorem sort_Sorted (l : List Nat) : Sorted (sort l) := by
  unfold sort
  induction l with
  | nil => apply Sorted.nil
  | cons h t ih =>
      apply insrt_Sorted
      cases t with
      | nil => simp [sort]; apply Sorted.nil
      | cons _ _ => simp at ih; exact ih
