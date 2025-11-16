import InsertionSort.Spec

-- Element of the inserted list is either the new element or
-- has an index from the original list
theorem insrt_getElem? (l: List Nat) (a i iv : Nat) :
  (insrt a l)[i]? = some iv → a = iv ∨ ∃ i': Nat, l[i']? = some iv := by
    intro h
    fun_induction insrt generalizing i iv with
    | case1 => -- l = nil
        simp
        simp [List.getElem?_singleton] at h
        exact h.right
    | case2 x xs h' => -- l = x :: xs, a ≤ x
        cases i with
        | zero => simp at h; exact Or.inl h
        | succ i' =>
            rw [List.getElem?_cons_succ] at h
            exact Or.inr ⟨i', h⟩
    | case3 x xs h' ih => -- l = x :: xs, ¬ a ≤ x
        cases i with
        | zero =>
            simp at h
            have res : (x :: xs)[0]? = some iv := by simp; exact h
            exact Or.inr ⟨0, res⟩
        | succ i' =>
            rw [List.getElem?_cons_succ] at h
            have ih' := ih i' iv h
            cases ih' with
            | inl h₁ => exact Or.inl h₁
            | inr h₁ =>
                rcases h₁ with ⟨j, hj⟩
                rw [← List.getElem?_cons_succ] at hj
                exact Or.inr ⟨j + 1, hj⟩

-- If a list is Sorted', then its tail is also Sorted'
theorem cons_Sorted' (x : Nat) (xs : List Nat) : Sorted' (x :: xs) → Sorted' xs := by
  intro h i j iv jv hij hi hj
  rw [← List.getElem?_cons_succ] at hi hj
  exact h (i + 1) (j + 1) iv jv (by omega)  hi hj

-- Insrt operation preserves Sorted' property
theorem insrt_Sorted' (a : Nat) (l: List Nat) : Sorted' l → Sorted' (insrt a l) := by
  induction l with
  | nil =>
      intro h i j iv jv hij hi hj
      simp [insrt, List.getElem?_singleton] at hi hj
      rw [← hi.right, ← hj.right]
      omega
  | cons x xs ih =>
      intro h i j iv jv hij hi hj
      by_cases ha : a ≤ x <;> simp_all [insrt]
      . -- a ≤ x
        match i, j with
        | 0, 0 => simp_all
        | 0, j + 1 =>
            simp_all
            have lem : (x :: xs)[0]? = x := by simp
            specialize h 0 j x jv (by omega) lem hj
            omega
        | i + 1, 0 => contradiction
        | i + 1, j + 1 =>
            simp_all
            exact h i j iv jv hij hi hj
      . -- ¬ a ≤ x
        have hsx : Sorted' xs := cons_Sorted' x xs h
        match i, j with
        | 0, 0 => simp_all
        | 0, j + 1 =>
            simp_all
            have hj' := insrt_getElem? xs a j jv hj
            cases hj' with
            | inl hj' => omega
            | inr hj' =>
                rcases hj' with ⟨j', hj'⟩
                rw [← List.getElem?_cons_succ] at hj'
                exact h 0 (j' + 1) iv jv (by omega) (by simp) hj'
        | i + 1, 0 => contradiction
        | i + 1, j + 1 =>
            simp_all
            exact ih i j iv jv hij hi hj

-- sort algorithm satisfies Sorted' property
theorem sort_Sorted' (l: List Nat) : Sorted' (sort l) := by
  induction l with
  | nil => simp [Sorted', sort]
  | cons h t ih => simp [sort]; exact insrt_Sorted' h (sort t) ih
