import AlgorithmsTUC.Basic
import Mathlib.Data.Prod.Basic

namespace MergeSortTUC
variable {A: Type u}[LinearOrder A]

def merge (l1 l2: List A): List A × ℕ :=
  match l1 with
  | [] =>
    (l2, 0)
  | hd::tl =>
    match l2 with
    | [] => (hd::tl, 0)
    | hd'::tl' =>
      if hd < hd'
      then
        let res := merge tl (hd'::tl')
        (hd::res.1, 1+res.2)
      else
        let res := merge (hd::tl) tl'
        (hd'::res.1, 1+res.2)

lemma mergeWorstCase (l1 l2 result: List A) (steps: ℕ) (hlen: l1.length = l2.length) (hsort: ∀ (i: ℕ) (hi: i < l1.length), l1.get (Fin.mk i hi) < l2.get  ⟨i, by rw [hlen] at hi; exact hi⟩) (hsort': ∀ (i: ℕ) (hi: i.succ < l1.length), l2.get ⟨i, by rw [hlen] at hi; apply Nat.lt_of_succ_lt hi⟩ < l1.get ⟨i.succ, hi⟩) (hres: merge l1 l2 = (result, steps)): steps = l1.length + l2.length - 1 :=
by
  induction l1 generalizing l2 result steps with
  | nil =>
    cases l2 with
    | nil =>
      simp
      simp[merge] at hres
      apply Eq.symm (And.right hres)
    | cons hd tl =>
      simp at hlen
  | cons hd tl ih =>
    cases l2 with
    | nil =>
      simp at hlen
    | cons hd' tl' =>
      simp[merge] at hres
      have hd_lt_hd': hd < hd' := by
        specialize hsort 0
        simp at hsort
        exact hsort
      simp [hd_lt_hd'] at hres
      cases tl with
      | nil =>
        cases tl' with
        | nil =>
          simp[merge] at hres
          rw [← And.right hres]
          simp
        | cons hdtl' tltl' =>
          simp at hlen
      | cons hdtl tltl =>
        simp[merge] at hres
        have n_hdtl_lt_hd': ¬ hdtl < hd' := by
          intro h
          apply lt_total hdtl hd' h
          specialize hsort' 0
          simp at hsort'
          exact hsort'
        simp[n_hdtl_lt_hd'] at hres
        simp
        rcases hres with ⟨_, hres⟩
        simp at hlen
        specialize ih tl' (merge (hdtl::tltl) tl').1 (steps-2)
        simp at ih
        specialize ih hlen
        rw [Nat.add_assoc _ 1 1, Nat.add_comm _ (1+1), Nat.add_assoc, ← ih]
        simp
        apply Eq.symm
        apply Nat.add_sub_of_le
        rw [← Nat.add_assoc] at hres
        simp at hres
        apply Nat.le.intro hres

        --Preservation of hsort and hsort'
        intro i hi
        specialize hsort i.succ
        simp at hsort
        apply hsort hi

        intro i hi
        specialize hsort' i.succ
        simp at hsort'
        apply hsort' hi

        -- we used the correct result
        rw [Prod.eq_iff_fst_eq_snd_eq]
        constructor
        simp

        simp
        rw [← hres, ← Nat.add_assoc 1 1 _, Nat.add_comm (1+1)]
        simp

--inspired by haskells terminology
def take (l: List A)(n: ℕ): List A :=
  match n with
  | 0 => []
  | Nat.succ m =>
    match l with
    | [] => []
    | hd::tl => hd::(take tl m)

lemma take_length (l: List A)(n: ℕ)(h: n ≤ l.length): (take l n).length = n := by
  induction n generalizing l with
  | zero => simp[take]
  | succ m ih =>
    cases l with
    | nil => simp at h
    | cons hd tl =>
      simp[take]
      simp at h
      apply ih tl h


def drop (l: List A)(n: ℕ): List A :=
  match n with
  | 0 => l
  | Nat.succ m =>
    match l with
    | [] => []
    | _::tl => drop tl m

lemma drop_length (l: List A)(n: ℕ)(h: n ≤ l.length): (drop l n).length = l.length - n := by
  induction n generalizing l with
  | zero => simp[drop]
  | succ m ih =>
    cases l with
    | nil => simp at h
    | cons hd tl =>
      simp[drop]
      simp at h
      apply ih tl h

def split (l: List A) (n: ℕ): List A × List A := (take l n, drop l n)

--#eval split [1,2,3,4,5] 2

lemma splitLen1 (l: List A) (h: l.length > 0): (split l (Nat.div l.length 2)).1.length < l.length := by
  unfold split
  simp
  rw [take_length]
  apply Nat.div2_smaller_self l.length
  exact h
  apply le_of_lt
  apply Nat.div2_smaller_self l.length
  exact h

lemma splitLen2 (l: List A) (h: l.length > 1): (split l (Nat.div l.length 2)).2.length < l.length := by
  unfold split
  simp
  rw [drop_length]
  apply Nat.sub_lt_left_of_lt_add
  apply le_of_lt
  apply Nat.div2_smaller_self l.length
  apply Nat.zero_lt_of_lt
  apply h

  apply Nat.lt_of_lt_of_le (m:= l.length.succ)
  simp
  rw [Nat.succ_eq_add_one, Nat.add_comm]
  apply Nat.add_le_add_right
  admit

  apply le_of_lt
  apply Nat.div2_smaller_self l.length
  apply Nat.zero_lt_of_lt
  apply h



def MergeSort (l: List A) : (List A × ℕ) :=
  if l.length <= 1
  then
    (l, 0)
  else
    let split := split l (Nat.div l.length 2)

    let leftResult := MergeSort split.1
    let rightResult := MergeSort split.2

    let mergeResult := merge leftResult.1 rightResult.1

    (mergeResult.1, mergeResult.2 + leftResult.2 + rightResult.2)
termination_by l.length
decreasing_by
  simp_wf
  rename_i h
  apply splitLen1
  apply Nat.gt_0_of_not_le_1 l.length h
  simp_wf
  apply splitLen2
  rename_i h
  simp at h
  exact h

lemma mergeSortKeepsLength (l: List A): l.length = (MergeSort l).1.length := by
  induction l.length using Nat.strongInductionOn generalizing l
  sorry

def isWorstCaseMergeSort (l: List A): Prop :=
  if l.length <= 1
  then True
  else
    let split := split l (Nat.div l.length 2)
    let leftResult := MergeSort split.1
    let rightResult := MergeSort split.2

    isWorstCaseMergeSort leftResult.1 ∧ isWorstCaseMergeSort rightResult.1 ∧ (merge leftResult.1 rightResult.1).2 = (leftResult.1.length + rightResult.1.length - 1)
termination_by l.length
decreasing_by
  simp_wf
  sorry
  sorry
