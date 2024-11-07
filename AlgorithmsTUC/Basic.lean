import Mathlib.Order.Defs

theorem lt_total{A: Type u}[LinearOrder A] (a b: A): a < b → b < a → False := by
  intro hab hba
  have a_lt_a: a < a := by
    apply lt_trans hab hba
  exact absurd a_lt_a (lt_irrefl a)
