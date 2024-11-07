import Mathlib

lemma two_def: 2 = 1 + 1 := by rfl

lemma test (n m: ℕ): n + m ≥ m := by exact Nat.le_add_left m n

theorem MergeSort.add_add_sub_add (n: ℕ) (hn: n >= 3): 1 + (1 + (n - 2 - 1)) = n - 1 := by
  cases n with
  | zero =>
    contradiction
  | succ n =>
    cases n with
    | zero =>
      contradiction
    | succ n =>
      simp[two_def]
      rw [Nat.add_sub_cancel', Nat.add_comm]
      aesop

theorem MergeSort.add3 (n m: ℕ): n + 1 + m = n + 1 + 1 + (m + 1) - 2 := by
  sorry

theorem MergeSort.ge_three (n m o: ℕ): n + 1 + 1 + (m +1) = o → o ≥ 3 := sorry

theorem lt_total{A: Type u}[LinearOrder A] (a b: A): a < b → b < a → False := sorry
