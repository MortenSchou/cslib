/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.BackwardCoverability
public import Cslib.Computability.PetriNets.Executable
public import Cslib.Foundations.Data.Search

/-! # An executable backward coverability algorithm

For nets given by multisets, the backward coverability iteration can be run on finite bases of
upward-closed sets. The minimal markings from which `t` fires into the markings above `b` is
`pre t + (b - post t)`. We iterate until every new basis element is already covered by an old
one; the abstract fixpoint theorem guarantees this happens after finitely many steps, and the
resulting basis decides coverability.

## Main definitions

- `ExecPetriNet.predBasis`, `ExecPetriNet.stepBasis`: one backward step on a finite basis.
- `ExecPetriNet.basisSeq`: the iteration from the target marking.
- `ExecPetriNet.Stable`: a decidable test that the iteration has converged.
- `ExecPetriNet.stableBasis`: the first stable iterate.

## Main statements

- `ExecPetriNet.coverable_iff_exists_basisSeq`: some iteration is stable, and from a stable
  iteration, coverability is decided by comparing with its finitely many basis elements.
- `ExecPetriNet.instDecidableCoverable`: coverability is decidable for executable nets.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

variable {Place Transition : Type*} [DecidableEq Place]

variable [Fintype Transition] (N : ExecPetriNet Place Transition)

/-- The minimal markings from which one firing leads above some element of `B`. -/
def predBasis (B : Finset (Multiset Place)) : Finset (Multiset Place) :=
  B.biUnion fun b => Finset.univ.image fun t => N.pre t + (b - N.post t)

/-- One backward step on a finite basis: keep `B` and add the minimal predecessors. -/
def stepBasis (B : Finset (Multiset Place)) : Finset (Multiset Place) :=
  B ∪ N.predBasis B

/-- The backward iteration starting from the single target marking `M`. -/
def basisSeq (M : Multiset Place) (n : ℕ) : Finset (Multiset Place) :=
  (N.stepBasis)^[n] {M}

/-- The iteration has converged if every new basis element is covered by an old one. -/
def Stable (B : Finset (Multiset Place)) : Prop :=
  ∀ x ∈ N.predBasis B, ∃ b ∈ B, b ≤ x

instance (B : Finset (Multiset Place)) : Decidable (N.Stable B) :=
  inferInstanceAs (Decidable (∀ x ∈ N.predBasis B, ∃ b ∈ B, b ≤ x))

open PetriNet

/-- The markings above some element of a finite basis. -/
def up (B : Finset (Multiset Place)) : Set (Marking Place) :=
  {M | ∃ b ∈ B, Multiset.toFinsupp b ≤ M}

theorem up_singleton (M : Multiset Place) : up {M} = Set.Ici (Multiset.toFinsupp M) := by
  ext; simp [up]

theorem predSet_up (B : Finset (Multiset Place)) :
    N.toPetriNet.predSet (up B) = up (N.predBasis B) := by
  ext M
  constructor
  · rintro ⟨t, M', ⟨R, rfl, rfl⟩, b, hb, hbM'⟩
    refine ⟨N.pre t + (b - N.post t), ?_, ?_⟩
    · exact Finset.mem_biUnion.2 ⟨b, hb, Finset.mem_image.2 ⟨t, Finset.mem_univ _, rfl⟩⟩
    · rw [map_add, toFinsupp_sub]
      exact add_le_add_right (tsub_le_iff_right.2 hbM') _
  · rintro ⟨x, hx, hle⟩
    obtain ⟨b, hb, hx⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.1 hx
    rw [map_add, toFinsupp_sub] at hle
    obtain ⟨R₀, hR₀⟩ := le_iff_exists_add.1 hle
    refine ⟨t, (Multiset.toFinsupp (b - N.post t) + R₀) + Multiset.toFinsupp (N.post t),
      ⟨Multiset.toFinsupp (b - N.post t) + R₀, ?_, rfl⟩, b, hb, ?_⟩
    · rw [hR₀, add_assoc, toFinsupp_sub]; rfl
    · calc Multiset.toFinsupp b ≤ Multiset.toFinsupp b - Multiset.toFinsupp (N.post t) +
            Multiset.toFinsupp (N.post t) := le_tsub_add
        _ ≤ _ := add_le_add_left (by rw [← toFinsupp_sub]; exact le_self_add) _

theorem backStep_up (B : Finset (Multiset Place)) :
    N.toPetriNet.backStep (up B) = up (N.stepBasis B) := by
  rw [PetriNet.backStep, predSet_up]
  ext M
  constructor
  · rintro (⟨b, hb, h⟩ | ⟨b, hb, h⟩)
    · exact ⟨b, Finset.mem_union_left _ hb, h⟩
    · exact ⟨b, Finset.mem_union_right _ hb, h⟩
  · rintro ⟨b, hb, h⟩
    rcases Finset.mem_union.1 hb with hb | hb
    · exact Or.inl ⟨b, hb, h⟩
    · exact Or.inr ⟨b, hb, h⟩

/-- The basis iteration describes the abstract backward iteration. -/
theorem backSeq_eq_up (M : Multiset Place) (n : ℕ) :
    N.toPetriNet.backSeq (Multiset.toFinsupp M) n = up (N.basisSeq M n) := by
  induction n with
  | zero => simp [PetriNet.backSeq, basisSeq, up_singleton]
  | succ n ih =>
    rw [PetriNet.backSeq_succ, ih, backStep_up]
    simp [basisSeq, Function.iterate_succ_apply']

theorem up_stepBasis_subset {B : Finset (Multiset Place)} (hs : N.Stable B) :
    up (N.stepBasis B) ⊆ up B := by
  rintro M ⟨b, hb, h⟩
  rcases Finset.mem_union.1 hb with hb | hb
  · exact ⟨b, hb, h⟩
  · obtain ⟨c, hc, hcb⟩ := hs b hb
    exact ⟨c, hc, (toFinsupp_le_iff.2 hcb).trans h⟩

/-- From a stable iteration, coverability is membership in the finite basis. -/
theorem coverable_iff_mem_up {M : Multiset Place} {n : ℕ} (hs : N.Stable (N.basisSeq M n))
    (M₀ : Marking Place) :
    N.toPetriNet.Coverable M₀ (Multiset.toFinsupp M) ↔ M₀ ∈ up (N.basisSeq M n) := by
  constructor
  · intro h
    obtain ⟨k, hk⟩ := PetriNet.coverable_iff_exists_mem_backSeq.1 h
    rcases le_total k n with hkn | hnk
    · rw [← backSeq_eq_up] at *
      exact PetriNet.backSeq_mono _ hkn hk
    · have key : ∀ k, n ≤ k →
          N.toPetriNet.backSeq (Multiset.toFinsupp M) k ⊆ up (N.basisSeq M n) := by
        intro k hnk
        induction k, hnk using Nat.le_induction with
        | base => rw [backSeq_eq_up]
        | succ k _ ih =>
          rw [PetriNet.backSeq_succ]
          intro x hx
          have hx' : x ∈ N.toPetriNet.backStep (up (N.basisSeq M n)) := by
            rcases hx with hx | ⟨t, M', hf, hM'⟩
            · exact Or.inl (ih hx)
            · exact Or.inr ⟨t, M', hf, ih hM'⟩
          rw [backStep_up] at hx'
          exact up_stepBasis_subset N hs hx'
      exact key k hnk hk
  · intro h
    rw [← backSeq_eq_up] at h
    exact PetriNet.coverable_of_mem_backSeq h

/-- From a stable iteration, coverability from a multiset marking is decided by comparing with
the finitely many basis elements. -/
theorem coverable_iff_exists_of_stable {M : Multiset Place} {n : ℕ}
    (hs : N.Stable (N.basisSeq M n)) (M₀ : Multiset Place) :
    N.toPetriNet.Coverable M₀ (Multiset.toFinsupp M) ↔
      ∃ b ∈ N.basisSeq M n, b ≤ M₀ := by
  rw [coverable_iff_mem_up N hs]
  constructor
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, toFinsupp_le_iff.1 h⟩
  · rintro ⟨b, hb, h⟩
    exact ⟨b, hb, toFinsupp_le_iff.2 h⟩

/-- Over a finite set of places, the basis iteration eventually stabilises. -/
theorem exists_stable [Finite Place] (M : Multiset Place) :
    ∃ n, N.Stable (N.basisSeq M n) := by
  obtain ⟨n, hn, -⟩ := PetriNet.exists_backSeq_fixpoint (N := N.toPetriNet) (Multiset.toFinsupp M)
  refine ⟨n, fun x hx => ?_⟩
  rw [backSeq_eq_up, backStep_up] at hn
  have : Multiset.toFinsupp x ∈ up (N.stepBasis (N.basisSeq M n)) :=
    ⟨x, Finset.mem_union_right _ hx, le_rfl⟩
  rw [hn] at this
  obtain ⟨b, hb, hle⟩ := this
  exact ⟨b, hb, toFinsupp_le_iff.1 hle⟩

/-- Coverability of `M` is decided by comparing with the finite basis of a stable iteration. -/
theorem coverable_iff_exists_basisSeq [Finite Place] (M : Multiset Place) :
    ∃ n, N.Stable (N.basisSeq M n) ∧ ∀ M₀ : Multiset Place,
      N.toPetriNet.Coverable M₀ (Multiset.toFinsupp M) ↔
        ∃ b ∈ N.basisSeq M n, b ≤ M₀ := by
  obtain ⟨n, hn⟩ := exists_stable N M
  exact ⟨n, hn, coverable_iff_exists_of_stable N hn⟩

/-- The first stable iterate of the backward iteration from the target `M`. -/
def stableBasis [Finite Place] (M : Multiset Place) : Finset (Multiset Place) :=
  searchIter N.stepBasis N.Stable {M} (exists_stable N M)

theorem stableBasis_spec [Finite Place] (M : Multiset Place) :
    ∃ n, N.stableBasis M = N.basisSeq M n ∧ N.Stable (N.stableBasis M) :=
  searchIter_spec N.stepBasis N.Stable {M} (exists_stable N M)

/-- Coverability is decided by comparing with the first stable basis. -/
theorem coverable_iff_exists_stableBasis [Finite Place] (M M₀ : Multiset Place) :
    N.toPetriNet.Coverable M₀ (Multiset.toFinsupp M) ↔
      ∃ b ∈ N.stableBasis M, b ≤ M₀ := by
  obtain ⟨n, hn, hs⟩ := stableBasis_spec N M
  rw [hn] at hs ⊢
  exact coverable_iff_exists_of_stable N hs M₀

/-- Coverability is decidable for executable nets over finitely many places.

The backward iteration is run until it stabilises, using `searchIter`. -/
instance instDecidableCoverable [Fintype Place] (M M₀ : Multiset Place) :
    Decidable (N.toPetriNet.Coverable M₀ (Multiset.toFinsupp M)) :=
  decidable_of_iff _ (coverable_iff_exists_stableBasis N M M₀).symm

end ExecPetriNet

end Cslib
