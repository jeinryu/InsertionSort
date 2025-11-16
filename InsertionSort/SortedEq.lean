import InsertionSort.Spec

-- if Sorted then Sorted'
theorem Sorted_Sorted' (l : List Nat) : Sorted l → Sorted' l := by
  intro h
  induction h with
  | nil => simp [Sorted']
  | singleton n =>
      intro i j iv jv h₁ h₂ h₃
      simp [List.getElem?_singleton] at h₂ h₃
      rw [h₂.left, h₃.left] at h₁
      simp [← h₂.right, ← h₃.right]
  | cons n m l hnm hml hml' =>
      intro i j iv jv h₁ h₂ h₃
      cases i with
      | zero =>
          simp at h₂
          simp [Sorted'] at hml'
          cases j with
          | zero =>
              simp at h₃
              simp [← h₂, ← h₃]
          | succ j' =>
              rw [List.getElem?_cons_succ] at h₃
              rw [← h₂]
              specialize hml' 0 j' m jv (by omega) (by simp) h₃
              omega
      | succ i' =>
          cases j with
          | zero => contradiction
          | succ j' =>
              rw [List.getElem?_cons_succ] at h₂ h₃
              simp [Sorted'] at hml'
              exact hml' i' j' iv jv (by omega) h₂ h₃

-- if Sorted' then Sorted
theorem Sorted'_Sorted (l : List Nat) : Sorted' l → Sorted l := by
  intro h
  induction l with
  | nil => apply Sorted.nil
  | cons x xs ih =>
      induction xs with
      | nil => apply Sorted.singleton
      | cons y ys ih' => -- goal : Sorted (x :: y :: ys)
          apply Sorted.cons
          . -- x ≤ y
            simp [Sorted'] at h
            exact h 0 1 x y (by omega) (by simp) (by simp)
          . -- Sorted (y :: ys)
            have lem : Sorted' (y :: ys) := by
              simp [Sorted']
              intro i j iv jv h₁ h₂ h₃
              rw [← List.getElem?_cons_succ] at h₂ h₃
              exact h (i + 1) (j + 1) iv jv (by omega) h₂ h₃
            exact ih lem
