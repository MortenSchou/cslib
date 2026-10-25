/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Monotonicity
public import Mathlib.Data.Finsupp.PWO

/-! # Coverability and pumping

A marking is *coverable* from `M₀` if some reachable marking is at least as large. A reachable
marking that can reach a strictly larger one can be pumped, which makes the net unbounded.

## Main definitions

- `PetriNet.Coverable`: a marking is coverable from another (`Cslib.WSTS.Coverable` of the
  marking graph).

## Main statements

- `Multiset.wellQuasiOrderedLE`: Dickson's lemma, multisets over a finite type are
  well-quasi-ordered.
- `PetriNet.not_bounded_of_pump`: if a reachable marking can reach a strictly larger one, then the
  net is unbounded. This is the easy half of the characterisation of unbounded nets.
-/

@[expose] public section

/-- Dickson's lemma for multisets: multisets over a finite type are well-quasi-ordered. This
instance is missing from Mathlib; it is transported from `Finsupp.wellQuasiOrderedLE`. -/
instance Multiset.wellQuasiOrderedLE {α : Type*} [Finite α] : WellQuasiOrderedLE (Multiset α) := by
  classical
  exact Finsupp.orderIsoMultiset.wellQuasiOrderedLE_iff.1 inferInstance

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- A marking `M` is coverable from `M₀` if some marking reachable from `M₀` is at least `M`.
This is `Cslib.WSTS.Coverable` for the marking graph. -/
abbrev Coverable (N : PetriNet Place Transition) (M₀ M : Marking Place) : Prop :=
  WSTS.Coverable N.lts M₀ M

@[grind →]
theorem Reachable.coverable {M₀ M : Marking Place} (h : M₀ ⇝[N] M) : N.Coverable M₀ M :=
  WSTS.CanReach.coverable h

@[grind →]
theorem Coverable.mono_target {M₀ M M' : Marking Place} (h : N.Coverable M₀ M) (hle : M' ≤ M) :
    N.Coverable M₀ M' :=
  WSTS.Coverable.mono_target h hle

/-- Coverability is monotone in the initial marking. -/
theorem Coverable.mono_source {M₁ M₂ M : Marking Place} (h : N.Coverable M₁ M) (hle : M₁ ≤ M₂) :
    N.Coverable M₂ M :=
  WSTS.Coverable.mono_source h hle

/-- Pumping: if a reachable marking `M₁` can reach a strictly larger marking `M₂`, the net is
unbounded at the initial marking. -/
theorem not_bounded_of_pump {M₀ M₁ M₂ : Marking Place} (h₁ : M₀ ⇝[N] M₁)
    (h₂ : M₁ ⇝[N] M₂) (hlt : M₁ < M₂) : ¬ N.Bounded M₀ := by
  rintro ⟨k, hk⟩
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hlt.le
  obtain ⟨p, hp⟩ := Multiset.exists_mem_of_ne_zero (s := K) (by rintro rfl; simp at hlt)
  have hpump : ∀ n : ℕ, M₁ ⇝[N] (M₁ + n • K) := by
    intro n
    induction n with
    | zero => simpa using .refl _ _
    | succ n ih =>
      have h := ih.trans (h₂.add (n • K))
      rwa [add_assoc, ← succ_nsmul'] at h
  refine hk _ (h₁.trans (hpump (k + 1))) p (le_add_left ?_)
  rw [← Multiset.nsmul_singleton]
  exact nsmul_le_nsmul_right (Multiset.singleton_le.2 hp) _

end PetriNet

end Cslib
