/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.Basic
public import Mathlib.Order.WellQuasiOrder
public import Mathlib.Order.UpperLower.Basic

/-! # Well-structured transition systems

A *well-structured transition system* (WSTS) is a labelled transition system whose states carry a
well-quasi-order for which the transitions are monotone: a larger state can simulate every step of
a smaller one, ending in a state that is again larger.

## Main definitions

- `Cslib.StronglyMonotone`: strong monotonicity of an `LTS` on a preorder.
- `Cslib.WSTS`: the class of well-structured transition systems on top of `LTS`: strongly monotone
  and well-quasi-ordered.
- `Cslib.WSTS.Coverable`: a state `t` is coverable from `s` if `s` reaches some `t' ≥ t`.

## Main statements

- `Cslib.WSTS.mTr_mono`, `Cslib.WSTS.canReach_mono`: monotonicity (strong, hence also for
  multistep transitions) lifts to executions.
- `Cslib.WSTS.Coverable.mono_source`: coverability is upward closed in the source.

## Design notes

We use *strong* monotonicity (a single step is matched by a single step with the same label),
which is the form satisfied by Petri nets and vector addition systems, and is the hypothesis of
the backward coverability algorithm. The weaker *reflexive* and *transitive* variants of Finkel
and Schnoebelen (a step is matched by a sequence of steps) are not formalised; the relevant
consequence, monotonicity of reachability (`canReach_mono`), is derived from strong monotonicity.

The order is a `Preorder`, as in the literature, and well-quasi-ordering is expressed by Mathlib's
`WellQuasiOrderedLE`.

## References

* [A. Finkel, P. Schnoebelen, *Well-structured transition systems everywhere!*]
  [FinkelSchnoebelen2001]
* [P. A. Abdulla, K. Cerans, B. Jonsson, Y.-K. Tsay, *Algorithmic Analysis of Programs with Well
  Quasi-Ordered Domains*][Abdulla2000]
-/

@[expose] public section

namespace Cslib

universe u v

/-- A labelled transition system on a preordered set of states is *(strongly) monotone* if a step
from a smaller state is matched, with the same label, from any larger state. This is the part of
the definition of a WSTS that does not involve the well-quasi-order, and it already suffices for
the soundness half of backward coverability. -/
class StronglyMonotone {State : Type u} {Label : Type v} [Preorder State]
    (lts : LTS State Label) : Prop where
  /-- A step from a smaller state is matched, with the same label, from any larger state. -/
  mono {s₁ s₂ s₁' : State} {μ : Label} :
    s₁ ≤ s₂ → lts.Tr s₁ μ s₁' → ∃ s₂', lts.Tr s₂ μ s₂' ∧ s₁' ≤ s₂'

/-- A *well-structured transition system*: a labelled transition system on a well-quasi-ordered
set of states, in which transitions are (strongly) monotone. -/
class WSTS {State : Type u} {Label : Type v} [Preorder State] (lts : LTS State Label) : Prop
    extends WellQuasiOrderedLE State, StronglyMonotone lts

namespace WSTS

variable {State : Type u} {Label : Type v} [Preorder State] {lts : LTS State Label}

variable (lts)

/-- A state `t` is coverable from `s` if some state reachable from `s` is at least `t`. -/
def Coverable (s t : State) : Prop :=
  ∃ t', lts.CanReach s t' ∧ t ≤ t'

variable {lts}

theorem CanReach.coverable {s t : State} (h : lts.CanReach s t) : Coverable lts s t :=
  ⟨t, h, le_rfl⟩

theorem Coverable.refl (s : State) : Coverable lts s s :=
  ⟨s, .refl lts s, le_rfl⟩

theorem Coverable.mono_target {s t t' : State} (h : Coverable lts s t) (hle : t' ≤ t) :
    Coverable lts s t' :=
  let ⟨t'', hr, ht⟩ := h
  ⟨t'', hr, hle.trans ht⟩

section

variable [StronglyMonotone lts]

/-- A multistep transition from `s₁` is matched from any `s₂ ≥ s₁` with the same labels. -/
theorem mTr_mono {s₁ s₁' s₂ : State} {μs : List Label} (h : lts.MTr s₁ μs s₁') (hle : s₁ ≤ s₂) :
    ∃ s₂', lts.MTr s₂ μs s₂' ∧ s₁' ≤ s₂' := by
  induction h generalizing s₂ with
  | refl => exact ⟨s₂, .refl, hle⟩
  | stepL htr _ ih =>
    obtain ⟨s₂', htr', hle'⟩ := StronglyMonotone.mono hle htr
    obtain ⟨s₃', hmtr, hle''⟩ := ih hle'
    exact ⟨s₃', .stepL htr' hmtr, hle''⟩

/-- Reachability is monotone: whatever a state reaches, a larger state reaches something larger. -/
theorem canReach_mono {s₁ s₁' s₂ : State} (h : lts.CanReach s₁ s₁') (hle : s₁ ≤ s₂) :
    ∃ s₂', lts.CanReach s₂ s₂' ∧ s₁' ≤ s₂' :=
  let ⟨μs, hμs⟩ := h
  let ⟨s₂', h₂, hle'⟩ := mTr_mono hμs hle
  ⟨s₂', ⟨μs, h₂⟩, hle'⟩

/-- Unlabelled steps are monotone. -/
theorem unlabelledTr_mono {s₁ s₁' s₂ : State} (h : lts.UnlabelledTr s₁ s₁') (hle : s₁ ≤ s₂) :
    ∃ s₂', lts.UnlabelledTr s₂ s₂' ∧ s₁' ≤ s₂' :=
  let ⟨_, h⟩ := h
  let ⟨s₂', h₂, hle'⟩ := StronglyMonotone.mono hle h
  ⟨s₂', ⟨_, h₂⟩, hle'⟩

/-- Coverability is monotone in the source. -/
theorem Coverable.mono_source {s₁ s₂ t : State} (h : Coverable lts s₁ t) (hle : s₁ ≤ s₂) :
    Coverable lts s₂ t :=
  let ⟨_, hr, ht⟩ := h
  let ⟨t'', hr', hle'⟩ := canReach_mono hr hle
  ⟨t'', hr', ht.trans hle'⟩

/-- The states from which `t` is coverable form an upper set. -/
theorem isUpperSet_coverable (t : State) : IsUpperSet {s | Coverable lts s t} :=
  fun _ _ hle h => h.mono_source hle

end

end WSTS

end Cslib
