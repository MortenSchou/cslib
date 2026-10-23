/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Cslib.Foundations.Semantics.LTS.Commutation
import Mathlib.Tactic.Abel

/-! # Commuting and non-conflicting transitions

Two transitions *commute* when neither consumes from a place that the other produces in. Then a
firing `t u` can be replaced by `u t`, with the same final marking. This makes the marking graph an
instance of `LTS.CommutesWith` for the relation `Commutes`, so that the generic Mazurkiewicz
equivalence `LTS.TraceEquiv N.Commutes` of firing sequences applies.

Two transitions are in *conflict* if they share a preset place, and at least one of them consumes
more than it produces there. Transitions that are not in conflict and are enabled at the same
marking can be fired in either order, which gives the diamond property of the marking graph at a
single marking. This is the notion of dependence of stubborn sets
(`Cslib.Computability.PetriNets.StubbornSets`), which does not go through `Commutes`.

## Main definitions

- `PetriNet.Commutes`: neither transition consumes from a place that the other produces in.
- `PetriNet.Conflict`: the transitions share a preset place at which one of them has a net loss.

## Main statements

- `PetriNet.lts_commutesWith`: the marking graph commutes commuting transitions.
- `PetriNet.Fires.diamond'`: transitions that are not in conflict and are enabled at the same
  marking can be fired in either order. `PetriNet.Fires.diamond` is the case of disjoint presets.
- `PetriNet.Fires.swap`: a firing `t u` where `u` consumes nothing produced by `t` can be fired as
  `u t`.
- `PetriNet.Fires.enabled_iff_of_noEffect`: a firing that has no net effect on the preset of `t`
  does not change whether `t` is enabled.

## References

* [A. Mazurkiewicz, *Trace theory*][Mazurkiewicz1987]
-/

@[expose] public section

namespace Finsupp

/-- If `a ≤ b + c` and `a` and `c` have no place in common, then `a ≤ b`. -/
theorem le_of_le_add_of_disjoint {α : Type*} {a b c : α →₀ ℕ} (h : a ≤ b + c)
    (hd : Disjoint a.support c.support) : a ≤ b := by
  refine Finsupp.le_def.2 fun p => ?_
  by_cases hp : a p = 0
  · rw [hp]
    exact Nat.zero_le _
  · have hc : c p = 0 := by
      by_contra hc
      exact Finset.disjoint_left.1 hd (Finsupp.mem_support_iff.2 hp) (Finsupp.mem_support_iff.2 hc)
    have := Finsupp.le_def.1 h p
    rwa [Finsupp.add_apply, hc, Nat.add_zero] at this

end Finsupp

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- The transitions `t` and `u` commute if neither consumes from a place that the other one
produces in. Both may consume from, or produce in, a common place. -/
def Commutes (N : PetriNet Place Transition) (t u : Transition) : Prop :=
  Disjoint (•[N] t).support (u •[N]).support ∧ Disjoint (•[N] u).support (t •[N]).support

/-- Commutation is symmetric. -/
theorem Commutes.symm {t u : Transition} (h : N.Commutes t u) : N.Commutes u t :=
  ⟨h.2, h.1⟩

/-- The transitions `t` and `u` are in conflict if some place is in both presets and at least one
of the transitions has fewer tokens there after firing than before. Two transitions that only read
a shared place are not in conflict. -/
def Conflict (N : PetriNet Place Transition) (t u : Transition) : Prop :=
  ∃ p, 0 < N.pre t p ∧ 0 < N.pre u p ∧ (N.post t p < N.pre t p ∨ N.post u p < N.pre u p)

/-- Conflict is symmetric. -/
theorem Conflict.symm {t u : Transition} (h : N.Conflict t u) : N.Conflict u t :=
  let ⟨p, h₁, h₂, h₃⟩ := h
  ⟨p, h₂, h₁, h₃.symm⟩

/-- Transitions with disjoint presets are not in conflict. -/
theorem not_conflict_of_disjoint {t u : Transition}
    (hd : Disjoint (•[N] t).support (•[N] u).support) : ¬ N.Conflict t u := by
  rintro ⟨p, h₁, h₂, -⟩
  exact Finset.disjoint_left.1 hd (Finsupp.mem_support_iff.2 h₁.ne')
    (Finsupp.mem_support_iff.2 h₂.ne')

/-- The diamond property: transitions that are not in conflict and are enabled at the same marking
can be fired in either order, and both orders lead to the same marking. -/
theorem Fires.diamond' {M M₁ M₂ : Marking Place} {t u : Transition} (hc : ¬ N.Conflict t u)
    (h₁ : M [t⟩[N] M₁) (h₂ : M [u⟩[N] M₂) : ∃ M₃, M₁ [u⟩[N] M₃ ∧ M₂ [t⟩[N] M₃ := by
  have hd : ∀ p, N.pre t p = 0 ∨ N.pre u p = 0 ∨
      (N.pre t p ≤ N.post t p ∧ N.pre u p ≤ N.post u p) := fun p => by
    by_contra hp
    exact hc ⟨p, by omega, by omega, by omega⟩
  obtain ⟨he₁, rfl⟩ := fires_iff.1 h₁
  obtain ⟨he₂, rfl⟩ := fires_iff.1 h₂
  have e₁ := Finsupp.le_def.1 he₁
  have e₂ := Finsupp.le_def.1 he₂
  have hu : N.pre u ≤ N.fire M t := Finsupp.le_def.2 fun p => by
    have := e₁ p; have := e₂ p; have := hd p
    simp only [fire, Finsupp.add_apply, Finsupp.tsub_apply]
    omega
  have ht : N.pre t ≤ N.fire M u := Finsupp.le_def.2 fun p => by
    have := e₁ p; have := e₂ p; have := hd p
    simp only [fire, Finsupp.add_apply, Finsupp.tsub_apply]
    omega
  refine ⟨N.fire (N.fire M t) u, fires_iff.2 ⟨hu, rfl⟩, fires_iff.2 ⟨ht, ?_⟩⟩
  ext p
  have := e₁ p; have := e₂ p; have := hd p
  simp only [fire, Finsupp.add_apply, Finsupp.tsub_apply]
  omega

/-- The diamond property for transitions with disjoint presets. -/
theorem Fires.diamond {M M₁ M₂ : Marking Place} {t u : Transition}
    (hd : Disjoint (•[N] t).support (•[N] u).support) (h₁ : M [t⟩[N] M₁) (h₂ : M [u⟩[N] M₂) :
    ∃ M₃, M₁ [u⟩[N] M₃ ∧ M₂ [t⟩[N] M₃ :=
  Fires.diamond' (not_conflict_of_disjoint hd) h₁ h₂

/-- A firing `t u` where `u` consumes nothing that `t` produces: the sequence `u t` is also
firable and reaches the same marking. -/
theorem Fires.swap {M M₁ M₃ : Marking Place} {t u : Transition}
    (hd : Disjoint (•[N] u).support (t •[N]).support) (h₁ : M [t⟩[N] M₁) (h₂ : M₁ [u⟩[N] M₃) :
    ∃ M₂, M [u⟩[N] M₂ ∧ M₂ [t⟩[N] M₃ := by
  obtain ⟨R, rfl, rfl⟩ := h₁
  obtain ⟨S, hS, rfl⟩ := h₂
  have hle : •[N] u ≤ R :=
    Finsupp.le_of_le_add_of_disjoint (le_iff_exists_add.2 ⟨S, hS⟩) hd
  obtain ⟨S', rfl⟩ := le_iff_exists_add.1 hle
  have hS' : S = S' + t •[N] :=
    add_left_cancel (a := •[N] u) (by rw [← hS]; abel)
  subst hS'
  exact ⟨•[N] t + S' + u •[N], ⟨•[N] t + S', by abel, by abel⟩,
    ⟨S' + u •[N], by abel, by abel⟩⟩

/-- The marking graph commutes commuting transitions. -/
theorem lts_commutesWith (N : PetriNet Place Transition) : N.lts.CommutesWith N.Commutes :=
  fun _ _ _ _ _ hc h₁ h₂ => Fires.swap hc.2 h₁ h₂

/-- A firing does not change the tokens of a place on which it has no net effect. -/
theorem Fires.apply_eq {M M' : Marking Place} {u : Transition} (h : M [u⟩[N] M') {p : Place}
    (hp : N.pre u p = N.post u p) : M p = M' p := by
  obtain ⟨R, rfl, rfl⟩ := h
  simp only [Finsupp.add_apply]
  omega

/-- Whether `t` is enabled is not changed by a firing of `u` that has no net effect on the preset
of `t`. -/
theorem Fires.enabled_iff_of_noEffect {M M' : Marking Place} {t u : Transition}
    (h : M [u⟩[N] M') (hp : ∀ p, 0 < N.pre t p → N.pre u p = N.post u p) :
    M [t⟩[N] ↔ M' [t⟩[N] := by
  simp only [Enabled, Finsupp.le_def]
  refine forall_congr' fun p => ?_
  by_cases h0 : N.pre t p = 0
  · simp only [h0, Nat.zero_le]
  · rw [h.apply_eq (hp p (Nat.pos_of_ne_zero h0))]

end PetriNet

end Cslib
