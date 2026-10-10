/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.CoverabilityBasis

/-! # Backward coverability

To decide whether a target marking `M` is coverable from `M₀`, work backwards from the
upward-closed set of markings above `M`. Let `Pre U` be the markings that can fire one transition
into `U`. Monotonicity of firing makes `Pre U` upward closed whenever `U` is. Starting from the
markings above `M` and repeatedly adding `Pre`, the union of the resulting ascending chain is the
set of markings from which `M` is coverable. Over finitely many places, Dickson's lemma (via the
finite basis of upward-closed sets) makes the chain stabilise after finitely many steps.

## Main definitions

- `PetriNet.pre`: the one-step predecessors of a set of markings.
- `PetriNet.backSeq`: the backward iteration from the markings above a target.

## Main statements

- `PetriNet.coverable_iff_exists_mem_backSeq`: coverability is the union of the iteration.
- `PetriNet.exists_backSeq_fixpoint`: over finitely many places, the iteration reaches a fixpoint
  that equals the set of markings from which the target is coverable.

## References

* [P. A. Abdulla, K. Cerans, B. Jonsson, Y.-K. Tsay, *Algorithmic Analysis of Programs with Well
  Quasi-Ordered Domains*][Abdulla2000]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} (N : PetriNet Place Transition)

/-- The markings from which a single firing leads into `U`. -/
def predSet (U : Set (Marking Place)) : Set (Marking Place) :=
  {M | ∃ t M', M [t⟩[N] M' ∧ M' ∈ U}

/-- One backward step: keep `U` and add its predecessors. -/
def backStep (U : Set (Marking Place)) : Set (Marking Place) :=
  U ∪ N.predSet U

/-- The backward iteration starting from the markings above the target `M`. -/
def backSeq (M : Marking Place) (n : ℕ) : Set (Marking Place) :=
  (N.backStep)^[n] (Set.Ici M)

variable {N}

theorem predSet_isUpperSet {U : Set (Marking Place)} (hU : IsUpperSet U) :
    IsUpperSet (N.predSet U) := by
  rintro M M'' hle ⟨t, M', hf, hM'⟩
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hle
  exact ⟨t, M' + K, hf.add K, hU le_self_add hM'⟩

theorem backStep_isUpperSet {U : Set (Marking Place)} (hU : IsUpperSet U) :
    IsUpperSet (N.backStep U) :=
  hU.union (predSet_isUpperSet hU)

theorem isUpperSet_backSeq (M : Marking Place) (n : ℕ) : IsUpperSet (N.backSeq M n) := by
  induction n with
  | zero => exact isUpperSet_Ici M
  | succ n ih => rw [backSeq, Function.iterate_succ_apply']; exact backStep_isUpperSet ih

theorem backSeq_succ (M : Marking Place) (n : ℕ) :
    N.backSeq M (n + 1) = N.backStep (N.backSeq M n) := by
  rw [backSeq, Function.iterate_succ_apply']; rfl

theorem backSeq_mono (M : Marking Place) : Monotone (N.backSeq M) :=
  monotone_nat_of_le_succ fun n => by
    rw [backSeq_succ]; exact Set.subset_union_left

/-- Everything in the backward iteration can cover the target. -/
theorem coverable_of_mem_backSeq {M M₀ : Marking Place} {n : ℕ} (h : M₀ ∈ N.backSeq M n) :
    N.Coverable M₀ M := by
  induction n generalizing M₀ with
  | zero => exact ⟨M₀, .refl _ _, h⟩
  | succ n ih =>
    rw [backSeq_succ] at h
    rcases h with h | ⟨t, M', hf, hM'⟩
    · exact ih h
    · obtain ⟨M'', hr, hle⟩ := ih hM'
      exact ⟨M'', hf.reachable.trans hr, hle⟩

/-- Every coverable marking appears in the backward iteration after as many steps as the
shortest covering firing sequence has transitions. -/
theorem mem_backSeq_of_mTr {M M₀ M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M₀ ts M') (hle : M ≤ M') : M₀ ∈ N.backSeq M ts.length := by
  induction h with
  | refl => exact hle
  | stepL htr _ ih =>
    rw [List.length_cons, backSeq_succ]
    exact Or.inr ⟨_, _, htr, ih hle⟩

/-- Coverability is the union of the backward iteration. -/
theorem coverable_iff_exists_mem_backSeq {M M₀ : Marking Place} :
    N.Coverable M₀ M ↔ ∃ n, M₀ ∈ N.backSeq M n :=
  ⟨fun ⟨_, ⟨_, hts⟩, hle⟩ => ⟨_, mem_backSeq_of_mTr hts hle⟩,
    fun ⟨_, h⟩ => coverable_of_mem_backSeq h⟩

/-- Over finitely many places, the backward iteration reaches a fixpoint, and that fixpoint is
exactly the set of markings from which the target is coverable. -/
theorem exists_backSeq_fixpoint [Finite Place] (M : Marking Place) :
    ∃ n, N.backStep (N.backSeq M n) = N.backSeq M n ∧
      ∀ M₀, N.Coverable M₀ M ↔ M₀ ∈ N.backSeq M n := by
  obtain ⟨B, hB, hiff⟩ := exists_finite_basis_coverable (N := N) M
  have hex : ∀ b ∈ B, ∃ n, b ∈ N.backSeq M n := fun b hb =>
    coverable_iff_exists_mem_backSeq.1 ((hiff b).2 ⟨b, hb, le_rfl⟩)
  choose! g hg using hex
  obtain ⟨n, hn⟩ := Set.Finite.bddAbove (hB.image g)
  have hmem : ∀ M₀, N.Coverable M₀ M ↔ M₀ ∈ N.backSeq M n := by
    intro M₀
    refine ⟨fun h => ?_, coverable_of_mem_backSeq⟩
    obtain ⟨b, hb, hbM₀⟩ := (hiff M₀).1 h
    exact isUpperSet_backSeq M n hbM₀
      (backSeq_mono M (hn ⟨b, hb, rfl⟩) (hg b hb))
  refine ⟨n, Set.Subset.antisymm ?_ Set.subset_union_left, hmem⟩
  intro M₀ hM₀
  rw [← backSeq_succ] at hM₀
  exact (hmem M₀).1 (coverable_of_mem_backSeq hM₀)

end PetriNet

end Cslib
