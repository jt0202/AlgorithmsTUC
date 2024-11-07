import Mathlib.Order.Defs
import Mathlib.Data.Nat.Defs


theorem lt_total{A: Type u}[LinearOrder A] (a b: A): a < b → b < a → False := by
  intro hab hba
  have a_lt_a: a < a := by
    apply lt_trans hab hba
  exact absurd a_lt_a (lt_irrefl a)

lemma Nat.div2_smaller_self (n: ℕ) (hn: n > 0): Nat.div n 2 < n := by
  apply Nat.div_lt_self hn
  simp

lemma Nat.gt_0_of_not_le_1 (n:ℕ) (h: ¬ n ≤ 1): n > 0 := by
  cases n with
  | zero => simp at h
  | succ m => simp
