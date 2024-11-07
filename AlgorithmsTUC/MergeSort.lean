import AlgorithmsTUC.Basic

namespace MergeSort
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
  induction' h: l1.length + l2.length using Nat.strongInductionOn generalizing l1 l2 result steps
  rename_i n ih
  cases l1 with
  | nil =>
    cases l2 with
    | nil =>
      unfold merge at hres
      simp at hres
      simp at h
      rw [← h,←  And.right hres]
    | cons hd tl => contradiction
  | cons hd tl =>
    cases l2 with
    | nil => contradiction
    | cons hd' tl' =>
      simp[merge] at hres
      have hd_lt_hd': hd < hd' := by
        specialize hsort 0
        simp at hsort
        exact hsort
      simp[hd_lt_hd'] at hres
      cases tl with
      | nil =>
        simp[merge] at hres
        rw [← And.right hres]
        cases tl' with
        | nil =>
          simp at h
          rw [← h]
        | cons hdtl tltl =>
          simp at hlen
      | cons hdtl tltl =>
        unfold merge at hres
        simp at hres
        simp at h

        have not_hdtl_lt_hd': ¬ hdtl < hd' := by
          specialize hsort' 0
          simp at hsort'
          apply lt_total hd' hdtl hsort'
        rcases hres with ⟨_, hsteps⟩
        rw [← hsteps]
        simp [not_hdtl_lt_hd']
        specialize ih (n-2)
        have n_minus_2: n - 2 < n := by
          rw [← h]
          simp
        specialize ih n_minus_2 (hdtl::tltl) tl' (merge (hdtl :: tltl) tl').1 (merge (hdtl :: tltl) tl').2
        simp at hlen
        simp at ih
        specialize ih hlen
        rw [ih]
        rw [add_add_sub_add]
        apply ge_three _ _ _ h

        intro i hi
        specialize hsort i.succ
        simp at hsort
        specialize hsort hi
        exact hsort

        intro i hi
        specialize hsort' i.succ
        simp at hsort'
        apply hsort'
        exact hi

        rw [← h]
        apply MergeSort.add3

def split (l: List A) (n: ℕ): List A × List A :=
  match n with
  | 0 => ([], l)
  | Nat.succ m =>
    match l with
    | [] => ([], [])
    | hd::tl =>
      let res := split tl m

      (hd::res.1, res.2)

lemma splitLen1 (l: List A): (split l (Nat.div l.length 2)).1.length < l.length := by
  sorry

lemma splitLen2 (l: List A): (split l (Nat.div l.length 2)).2.length < l.length := by
  sorry

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
  apply splitLen1
  simp_wf
  apply splitLen2
