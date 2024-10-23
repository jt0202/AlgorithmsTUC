import Mathlib.Algebra.Order.Floor

variable {A: Type u} [LinearOrder A]

inductive typeWithBorders (A: Type u)
| mk: A → typeWithBorders A
| min: typeWithBorders A
| max: typeWithBorders A

def typeWithBorders.le (A: Type u) [LinearOrder A] (a b: typeWithBorders A): Prop :=
  match a with
  | typeWithBorders.mk a' =>
    match b with
    | typeWithBorders.mk b' => a' ≤ b'
    | typeWithBorders.min => False
    | typeWithBorders.max => True
  | typeWithBorders.min => True
  | typeWithBorders.max =>
    match b with
      | typeWithBorders.mk _ => False
      | typeWithBorders.min => False
      | typeWithBorders.max => True

instance decidableLE (A: Type u) [LinearOrder A]: DecidableRel ( typeWithBorders.le A) := by
  rename_i LinOrdA
  unfold DecidableRel
  intro a b
  unfold typeWithBorders.le
  cases a with
  | mk a' =>
    cases b with
    | mk b' =>
      simp
      apply LinOrdA.decidableLE
    | min =>
      exact instDecidableFalse
    | max =>
      exact instDecidableTrue
  | min =>
    exact instDecidableTrue
  | max =>
    cases b with
    | mk b' =>
      exact instDecidableFalse
    | min =>
      exact instDecidableFalse
    | max =>
      exact instDecidableTrue

lemma typeWithBorders.le_refl (a: typeWithBorders A): typeWithBorders.le A a a :=by
  unfold le
  cases a with
  | mk a' => simp
  | min => simp
  | max => simp

lemma typeWithBorders.le_trans (a b c: typeWithBorders A) (hab: le A a b)(hbc: le A b c): le A a c:= by
  rename_i linA
  unfold le at *
  cases a with
  | mk a' =>
    cases b with
    | mk b' =>
      cases c with
      | mk c' =>
        simp at *
        apply linA.le_trans
        apply hab
        apply hbc
      | min =>
        simp at *
      | max => unfold le at *; simp at *
    | min =>
      simp at *
    | max =>
      cases c with
      | mk c' => simp at *
      | min => simp at *
      | max => simp
  | min =>
    simp
  | max =>
    cases b with
    | mk b' => simp at *
    | min => simp at *
    | max =>
      cases c with
      | mk c' => simp at *
      | min => simp at *
      | max => simp at *

lemma typeWithBorders.le_antisymm (a b: typeWithBorders A) (hab: le A a b) (hba: le A b a): a = b := by
  rename_i LinOrdA
  unfold le at *
  cases a with
  | mk a' =>
    cases b with
    | mk b' =>
      simp at *
      apply LinOrdA.le_antisymm
      apply hab
      apply hba
    | min => simp at *
    | max => simp at *
  | min =>
    cases b with
    | mk b' => simp  at *
    | min => rfl
    | max => simp at *
  | max =>
    cases b with
    | mk b' => simp at *
    | min => simp at *
    | max => rfl


lemma typeWithBorders.le_total (a b: typeWithBorders A): le A a b ∨ le A b a := by
  rename_i LinOrdA
  unfold le
  cases a with
  | mk a' =>
    cases b with
    | mk b' =>
      simp
      apply LinOrdA.le_total
    | min => simp
    | max => simp
  | min =>
    cases b with
    | mk b' => simp
    | min => simp
    | max => simp
  | max =>
    cases b with
    | mk b' => simp
    | min => simp
    | max => simp



instance (A: Type u) [LinearOrder A]: LinearOrder (typeWithBorders A) where
  le := typeWithBorders.le A
  le_refl := typeWithBorders.le_refl
  le_trans := typeWithBorders.le_trans
  le_antisymm := typeWithBorders.le_antisymm
  le_total := typeWithBorders.le_total
  decidableLE := decidableLE A

--Search Framework
def List.sorted (l: List A): Prop :=
  match l with
  | nil => True
  | hd::tl => tl.sorted ∧  ∀ (a:A), a ∈ tl →  hd ≤ a

def generalizedArrayGet (l: List A) (pos: ℤ): typeWithBorders A :=
  match pos with
  | Int.ofNat n =>
    if h:n < l.length
    then typeWithBorders.mk (l.get (Fin.mk n h))
    else typeWithBorders.max
  | Int.negSucc _ => typeWithBorders.min

structure searchStrategy where
  strat: ℕ → ℕ → ℕ
  valid: ∀ (u l: ℕ), (u - l > 1) → strat u l > l ∧ u > strat u l


def generalizedSearchHelper (l: List A)(x:A)(upper lower:ℕ )(searchStrategy: searchStrategy) (numComp: ℕ): ℤ × ℕ :=
  if upper - lower > 0
  then
    let middle := searchStrategy.strat upper lower

    if generalizedArrayGet l middle ≤ typeWithBorders.mk x
    then
      generalizedSearchHelper l x upper middle searchStrategy (numComp + 1)
    else
      generalizedSearchHelper l x middle lower searchStrategy (numComp + 1)
  else
    (Int.sub lower 1, numComp)
termination_by upper - lower
decreasing_by
  simp_wf
  admit
  simp_wf
  admit



def generalizedSearch (l: List A) (x:A) (searchStrategy: searchStrategy): ℤ × ℕ := generalizedSearchHelper l x 0 l.length searchStrategy 0

theorem binarySearchCorrect (l: List A) (sort: l.sorted) (x:A) (idx: ℤ)(runs: ℕ) (searchStrategy: searchStrategy) (h: generalizedSearch l x searchStrategy = (idx, runs)) : generalizedArrayGet l idx <= typeWithBorders.mk x ∧ ¬ generalizedArrayGet l (idx + 1) = typeWithBorders.mk  x := by
  sorry

-- binarySearch

def binarySearchStrategy: searchStrategy where
  strat := fun u l => (u+l)/2
  valid := sorry


def binarySearch (l: List A) (x:A): ℤ × ℕ := generalizedSearch l x binarySearchStrategy

--Square root
