/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.WSTS.Basic

/-! # Backward coverability for well-structured transition systems

To decide whether `t` is coverable from `s`, work backwards from the upper set above `t`. Let
`predSet U` be the states with a step into `U`. Monotonicity makes `predSet U` an upper set
whenever `U` is. Starting from the states above `t` and repeatedly adding `predSet`, the union of
the resulting ascending chain is the set of states from which `t` is coverable. Because the order
is a well-quasi-order, ascending chains of upper sets stabilise, so the chain reaches a fixpoint
after finitely many steps.

## Main definitions

- `Cslib.WSTS.predSet`: the one-step predecessors of a set of states.
- `Cslib.WSTS.backStep`: keep a set and add its predecessors.
- `Cslib.WSTS.backSeq`: the backward iteration from the states above a target.

## Main statements

- `Cslib.WSTS.exists_stabilises`: ascending chains of upper sets in a well-quasi-order stabilise.
- `Cslib.WSTS.coverable_iff_exists_mem_backSeq`: coverability is the union of the iteration.
- `Cslib.WSTS.exists_backSeq_fixpoint`: the iteration reaches a fixpoint, which is exactly the set
  of states from which the target is coverable.

## References

* [P. A. Abdulla, K. Cerans, B. Jonsson, Y.-K. Tsay, *Algorithmic Analysis of Programs with Well
  Quasi-Ordered Domains*][Abdulla2000]
-/

@[expose] public section

namespace Cslib

namespace WSTS

/-- In a well-quasi-order, every ascending chain of upper sets has two equal consecutive members.
Otherwise one picks `x n ∈ U (n + 1) \ U n`; two indices `i < j` with `x i ≤ x j` give
`x j ∈ U j`, a contradiction. -/
theorem exists_stabilises {α : Type*} [Preorder α] [WellQuasiOrderedLE α] (U : ℕ → Set α)
    (hup : ∀ n, IsUpperSet (U n)) (hmono : Monotone U) : ∃ n, U (n + 1) ⊆ U n := by
  by_contra hcon
  simp only [not_exists, Set.not_subset] at hcon
  choose x hx hxn using hcon
  obtain ⟨i, j, hij, hle⟩ := wellQuasiOrdered_le x
  exact hxn j (hup j hle (hmono (Nat.succ_le_of_lt hij) (hx i)))

variable {State : Type*} {Label : Type*} [Preorder State] (lts : LTS State Label)

/-- The states with a step into `U`. -/
def predSet (U : Set State) : Set State :=
  {s | ∃ μ s', lts.Tr s μ s' ∧ s' ∈ U}

/-- One backward step: keep `U` and add its predecessors. -/
def backStep (U : Set State) : Set State :=
  U ∪ predSet lts U

/-- The backward iteration starting from the states above the target `t`. -/
def backSeq (t : State) (n : ℕ) : Set State :=
  (backStep lts)^[n] (Set.Ici t)

variable {lts}

theorem predSet_isUpperSet [StronglyMonotone lts] {U : Set State} (hU : IsUpperSet U) :
    IsUpperSet (predSet lts U) := by
  rintro s₁ s₂ hle ⟨μ, s₁', htr, hs₁'⟩
  obtain ⟨s₂', htr', hle'⟩ := StronglyMonotone.mono hle htr
  exact ⟨μ, s₂', htr', hU hle' hs₁'⟩

theorem backStep_isUpperSet [StronglyMonotone lts] {U : Set State} (hU : IsUpperSet U) :
    IsUpperSet (backStep lts U) :=
  hU.union (predSet_isUpperSet hU)

theorem backSeq_succ (t : State) (n : ℕ) :
    backSeq lts t (n + 1) = backStep lts (backSeq lts t n) := by
  rw [backSeq, Function.iterate_succ_apply']; rfl

theorem isUpperSet_backSeq [StronglyMonotone lts] (t : State) (n : ℕ) :
    IsUpperSet (backSeq lts t n) := by
  induction n with
  | zero => exact isUpperSet_Ici t
  | succ n ih => rw [backSeq_succ]; exact backStep_isUpperSet ih

theorem backSeq_mono (t : State) : Monotone (backSeq lts t) :=
  monotone_nat_of_le_succ fun n => by
    rw [backSeq_succ]; exact Set.subset_union_left

/-- Everything in the backward iteration can cover the target. -/
theorem coverable_of_mem_backSeq {t s : State} {n : ℕ} (h : s ∈ backSeq lts t n) :
    Coverable lts s t := by
  induction n generalizing s with
  | zero => exact ⟨s, .refl lts s, h⟩
  | succ n ih =>
    rw [backSeq_succ] at h
    rcases h with h | ⟨μ, s', htr, hs'⟩
    · exact ih h
    · obtain ⟨t', hr, hle⟩ := ih hs'
      exact ⟨t', (LTS.CanReach.single htr).trans hr, hle⟩

/-- Every coverable state appears in the backward iteration after as many steps as the shortest
covering execution has transitions. -/
theorem mem_backSeq_of_mTr {t s s' : State} {μs : List _} (h : lts.MTr s μs s') (hle : t ≤ s') :
    s ∈ backSeq lts t μs.length := by
  induction h with
  | refl => exact hle
  | stepL htr _ ih =>
    rw [List.length_cons, backSeq_succ]
    exact Or.inr ⟨_, _, htr, ih hle⟩

/-- Coverability is the union of the backward iteration. -/
theorem coverable_iff_exists_mem_backSeq {t s : State} :
    Coverable lts s t ↔ ∃ n, s ∈ backSeq lts t n :=
  ⟨fun ⟨_, ⟨_, hts⟩, hle⟩ => ⟨_, mem_backSeq_of_mTr hts hle⟩,
    fun ⟨_, h⟩ => coverable_of_mem_backSeq h⟩

/-- Once the backward iteration reaches a fixpoint, it stays there. -/
theorem backSeq_eq_of_fixpoint {t : State} {n : ℕ} (h : backStep lts (backSeq lts t n) =
    backSeq lts t n) {m : ℕ} (hm : n ≤ m) : backSeq lts t m = backSeq lts t n := by
  induction m, hm using Nat.le_induction with
  | base => rfl
  | succ m _ ih => rw [backSeq_succ, ih, h]

/-- The backward iteration reaches a fixpoint after finitely many steps, and that fixpoint is
exactly the set of states from which the target is coverable. -/
theorem exists_backSeq_fixpoint [WSTS lts] (t : State) :
    ∃ n, backStep lts (backSeq lts t n) = backSeq lts t n ∧
      ∀ s, Coverable lts s t ↔ s ∈ backSeq lts t n := by
  obtain ⟨n, hn⟩ := exists_stabilises (backSeq lts t) (isUpperSet_backSeq t) (backSeq_mono t)
  have hfix : backStep lts (backSeq lts t n) = backSeq lts t n :=
    Set.Subset.antisymm (backSeq_succ t n ▸ hn) Set.subset_union_left
  refine ⟨n, hfix, fun s => ⟨fun h => ?_, coverable_of_mem_backSeq⟩⟩
  obtain ⟨m, hm⟩ := coverable_iff_exists_mem_backSeq.1 h
  rw [← backSeq_eq_of_fixpoint hfix (le_max_left n m)]
  exact backSeq_mono t (le_max_right n m) hm

end WSTS

end Cslib
