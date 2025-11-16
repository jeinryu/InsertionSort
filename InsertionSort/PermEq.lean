import InsertionSort.Spec
open Multiset

namespace Multiset
theorem Perm_Contents (al bl: List Nat) : List.Perm al bl → contents al = contents bl := by
  intro h
  induction h with
  | nil => rfl
  | cons x h₁ h₂ => simp [contents, h₂]
  | swap x y l => simp [contents, union_swap]
  | trans h₁ h₂ ih₁ ih₂ => rw [ih₁, ih₂]

theorem Contents_nil_inv (l : List Nat) : (∀ x, 0 = contents l x) → l = [] := by
  intro h
  cases l with
  | nil => rfl
  | cons x xs =>
      specialize h x
      simp [contents, union, singleton] at h
      omega
theorem Contents_cons_inv (l : List Nat) (x n : Nat) :
n + 1 = contents l x →
∃ l₁ l₂ , l = l₁ ++ x :: l₂ ∧ contents (l₁ ++ l₂) x = n := by
  intro h
  induction l with
  | nil => contradiction
  | cons a al ih =>
      simp [contents, union, singleton] at h
      by_cases h₁ : x = a <;> simp_all
      . -- x = a
        rw [Nat.add_comm] at h
        exists [], al
        simp; omega
      . -- x ≠ a
        match ih with
        | ⟨l₁, ⟨l₂, ih⟩⟩ =>
            exists a :: l₁, l₂
            constructor
            . rw [ih.left]; rfl
            . simp [contents, union, singleton, h₁, ih.right]

theorem Contents_insert_other (l₁ l₂ : List Nat) (x y : Nat) :
  y ≠ x → contents (l₁ ++ x :: l₂) y = contents (l₁ ++ l₂) y := by
    intro h
    induction l₁ with
    | nil => simp [contents, union, singleton, h]
    | cons a al ih => simp [contents, union, ih]

theorem Contents_Perm (al bl : List Nat) :
  contents al = contents bl → List.Perm al bl := by
    intro h
    induction al generalizing bl with
    | nil =>
        simp; apply Contents_nil_inv
        intro x
        simp [← h, contents, empty]
    | cons a al ih =>
        have h' := congrFun h
        cases bl with
        | nil =>
            simp [contents, union, singleton, empty] at h'
            specialize h' a; omega
        | cons b bl =>
            simp [contents, union, singleton] at h'
            by_cases h₁ : a = b
            . -- a = b
              rw [h₁]
              apply List.Perm.cons
              have h₂ : contents al = contents bl := by
                funext x
                specialize h' x
                by_cases h₂ : x = a <;> simp_all
              exact ih bl h₂
            . -- a ≠ b
              have h₂ := h' a
              have h₃ := h' b
              simp [h₁] at h₂
              simp [eq_comm, h₁] at h₃
              rw [Nat.add_comm] at h₂ h₃
              have h₄ := (Contents_cons_inv bl a (contents al a)) h₂
              obtain ⟨l₁, l₂, rfl, hcontents⟩ := h₄
              have lem : contents al = contents (b :: (l₁ ++ l₂)) := by
                funext x
                by_cases hb : x = b
                . -- x = b
                  have hab := Contents_insert_other l₁ l₂ a b (by omega)
                  simp [contents, union, singleton, hb]
                  rw [hab, Nat.add_comm] at h₃; exact h₃
                . -- x ≠ b
                  simp [contents, union, singleton, hb]
                  by_cases ha : x = a
                  . rw [ha]; omega -- x = a
                  . -- x ≠ a
                    specialize h' x
                    simp [ha, hb] at h'
                    have hc := Contents_insert_other l₁ l₂ a x (by omega)
                    omega
              specialize ih (b :: (l₁ ++ l₂)) lem
              have h₄ : List.Perm (b :: a :: l₁ ++ l₂) (b :: l₁ ++ a :: l₂) := by
                apply List.Perm.symm
                apply List.Perm.cons
                apply List.perm_middle
              have h₅ : List.Perm (a :: b :: l₁ ++ l₂) (b :: a :: l₁ ++ l₂) := by apply List.Perm.swap
              rw [← List.perm_cons a] at ih
              exact List.Perm.trans (List.Perm.trans ih h₅) h₄
namespace Multiset
