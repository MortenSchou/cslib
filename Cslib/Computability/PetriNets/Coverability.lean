/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Monotonicity

/-! # Coverability and pumping

A marking is *coverable* from `M₀` if some reachable marking is at least as large. A reachable
marking that can reach a strictly larger one can be pumped, which makes the net unbounded.

## Main definitions

- `PetriNet.Coverable`: a marking is coverable from another.

## Main statements

- `PetriNet.not_bounded_of_pump`: if a reachable marking can reach a strictly larger one, then the
  net is unbounded. This is the easy half of the characterisation of unbounded nets.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- A marking `M` is coverable from `M₀` if some marking reachable from `M₀` is at least `M`. -/
def Coverable (N : PetriNet Place Transition) (M₀ M : Marking Place) : Prop :=
  ∃ M', M₀ ⇝[N] M' ∧ M ≤ M'

@[grind →]
theorem Reachable.coverable {M₀ M : Marking Place} (h : M₀ ⇝[N] M) : N.Coverable M₀ M :=
  ⟨M, h, le_rfl⟩

@[grind →]
theorem Coverable.mono_target {M₀ M M' : Marking Place} (h : N.Coverable M₀ M) (hle : M' ≤ M) :
    N.Coverable M₀ M' :=
  let ⟨M'', hr, hM⟩ := h
  ⟨M'', hr, hle.trans hM⟩

/-- Coverability is monotone in the initial marking. -/
theorem Coverable.mono_source {M₁ M₂ M : Marking Place} (h : N.Coverable M₁ M) (hle : M₁ ≤ M₂) :
    N.Coverable M₂ M :=
  let ⟨_, hr, hM⟩ := h
  let ⟨M'', hr', hle'⟩ := hr.mono hle
  ⟨M'', hr', hM.trans hle'⟩

/-- Pumping: if a reachable marking `M₁` can reach a strictly larger marking `M₂`, the net is
unbounded at the initial marking. -/
theorem not_bounded_of_pump {M₀ M₁ M₂ : Marking Place} (h₁ : M₀ ⇝[N] M₁)
    (h₂ : M₁ ⇝[N] M₂) (hlt : M₁ < M₂) : ¬ N.Bounded M₀ := by
  rintro ⟨k, hk⟩
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hlt.le
  have hK : K ≠ 0 := by
    rintro rfl
    simp at hlt
  obtain ⟨p, hp⟩ : ∃ p, K p ≠ 0 := by
    by_contra hcon
    exact hK (Finsupp.ext fun p => by_contra fun h => hcon ⟨p, h⟩)
  have hpump : ∀ n : ℕ, M₁ ⇝[N] (M₁ + n • K) := by
    intro n
    induction n with
    | zero => simpa using .refl _ _
    | succ n ih =>
      have h := ih.trans (h₂.add (n • K))
      have e : M₁ + K + n • K = M₁ + (n + 1) • K := by
        rw [succ_nsmul]; ac_rfl
      rwa [e] at h
  have hreach := h₁.trans (hpump (k + 1))
  have hle := hk _ hreach p
  have hKp : 1 ≤ K p := Nat.one_le_iff_ne_zero.2 hp
  simp only [Finsupp.add_apply, Finsupp.smul_apply, smul_eq_mul] at hle
  have := Nat.mul_le_mul_left (k + 1) hKp
  omega

end PetriNet

end Cslib
