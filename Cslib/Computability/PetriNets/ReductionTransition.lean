/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Labelled
public import Cslib.Foundations.Semantics.LTS.Bisimulation

/-! # Fusion of parallel transitions

Two transitions are *parallel* if they are distinct and have the same preset and postset. Deleting
one of them does not change which markings are reachable, and the deleted transition behaves
exactly like the one that remains. The marking graphs, with the deleted transition relabelled by
its twin, are equal, hence bisimilar.

## Main definitions

- `PetriNet.removeTransition`: the net with a transition deleted.
- `PetriNet.ParallelTransitions`: two distinct transitions with equal preset and postset;
  decidable when places and transitions have decidable equality.

## Main statements

- `PetriNet.reachable_removeTransition_iff`: the reachable markings are unchanged.
- `PetriNet.labelledLts_removeTransition`: the marking graph of the reduced net is that of `N`,
  with the deleted transition relabelled by its twin.
- `PetriNet.ParallelTransitions.bisimilar`: the marking graphs of `N` and of the reduced net, with
  the deleted transition relabelled by its twin, are bisimilar at every marking.
- `PetriNet.ParallelTransitions.live_removeTransition_iff`,
  `PetriNet.ParallelTransitions.bounded_removeTransition_iff`,
  `PetriNet.ParallelTransitions.safe_removeTransition_iff`,
  `PetriNet.ParallelTransitions.dead_removeTransition_iff`: liveness, boundedness, safeness and
  deadlocks are preserved.

Fusion of series transitions is in `Cslib.Computability.PetriNets.SeriesReduction`, and
elimination of self-loop transitions is in `Cslib.Computability.PetriNets.SelfLoopTransition`.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- The net with the transition `t₀` deleted. -/
def removeTransition (N : PetriNet Place Transition) (t₀ : Transition) :
    PetriNet Place {t // t ≠ t₀} where
  pre t := N.pre t
  post t := N.post t

section

variable {N : PetriNet Place Transition} {t₁ t₂ : Transition}

/-- The preset of a transition of the reduced net is that of the underlying transition of `N`. -/
@[simp]
theorem removeTransition_pre (t : {t // t ≠ t₂}) : (N.removeTransition t₂).pre t = N.pre t.1 :=
  rfl

/-- The postset of a transition of the reduced net is that of the underlying transition of `N`. -/
@[simp]
theorem removeTransition_post (t : {t // t ≠ t₂}) : (N.removeTransition t₂).post t = N.post t.1 :=
  rfl

/-- Firing a transition of the reduced net is firing the underlying transition of `N`. -/
theorem fires_removeTransition {M M' : Marking Place} {t : {t // t ≠ t₂}} :
    M [t⟩[N.removeTransition t₂] M' ↔ M [t.1⟩[N] M' := Iff.rfl

/-- A transition of the reduced net is enabled exactly when the underlying transition of `N` is. -/
theorem enabled_removeTransition {M : Marking Place} {t : {t // t ≠ t₂}} :
    M [t⟩[N.removeTransition t₂] ↔ M [t.1⟩[N] := Iff.rfl

/-- Reachability in the net with a transition deleted is reachability in the net. -/
theorem reachable_of_reachable_removeTransition {M M' : Marking Place}
    (h : M ⇝[N.removeTransition t₂] M') : M ⇝[N] M' := by
  obtain ⟨ts, hts⟩ := h
  induction hts with
  | refl => exact Reachable.refl N _
  | stepL htr _ ih => exact (Fires.reachable (N := N) htr).trans ih

/-- Two transitions are *parallel* if they are distinct and have the same preset and postset. -/
def ParallelTransitions (N : PetriNet Place Transition) (t₁ t₂ : Transition) : Prop :=
  t₁ ≠ t₂ ∧ N.pre t₁ = N.pre t₂ ∧ N.post t₁ = N.post t₂

instance [DecidableEq Place] [DecidableEq Transition] (N : PetriNet Place Transition)
    (t₁ t₂ : Transition) : Decidable (N.ParallelTransitions t₁ t₂) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

namespace ParallelTransitions

variable (h : N.ParallelTransitions t₁ t₂)
include h

/-- Parallel transitions are enabled at the same markings. -/
theorem enabled_iff {M : Marking Place} : M [t₁⟩[N] ↔ M [t₂⟩[N] := by
  simp only [Enabled, h.2.1]

/-- Parallel transitions have the same effect. -/
theorem fires_iff {M M' : Marking Place} : M [t₁⟩[N] M' ↔ M [t₂⟩[N] M' := by
  simp only [Fires, h.2.1, h.2.2]

/-- A step of `N` is a step of the net with `t₂` deleted, using `t₁` in place of `t₂`. -/
theorem exists_fires_removeTransition {M M' : Marking Place} {t : Transition}
    (htr : M [t⟩[N] M') : ∃ s : {t // t ≠ t₂}, M [s⟩[N.removeTransition t₂] M' := by
  by_cases ht : t = t₂
  · subst ht
    exact ⟨⟨t₁, h.1⟩, h.fires_iff.2 htr⟩
  · exact ⟨⟨t, ht⟩, htr⟩

/-- Deleting a parallel transition does not change the reachable markings. -/
theorem reachable_removeTransition_iff {M M' : Marking Place} :
    (M ⇝[N.removeTransition t₂] M') ↔ M ⇝[N] M' := by
  constructor
  · exact reachable_of_reachable_removeTransition
  · rintro ⟨ts, hts⟩
    induction hts with
    | refl => exact Reachable.refl _ _
    | stepL htr _ ih =>
      obtain ⟨s, hs⟩ := h.exists_fires_removeTransition htr
      exact (Fires.reachable hs).trans ih

/-- The marking graph of the reduced net is that of `N`, with `t₂` relabelled `t₁`. -/
theorem labelledLts_removeTransition [DecidableEq Transition] :
    N.labelledLts (Function.update id t₂ t₁) =
      (N.removeTransition t₂).labelledLts Subtype.val := by
  ext M a M'
  simp only [labelledLts_tr_iff]
  constructor
  · rintro ⟨t, rfl, htr⟩
    by_cases ht : t = t₂
    · subst ht
      exact ⟨⟨t₁, h.1⟩, by simp, h.fires_iff.2 htr⟩
    · exact ⟨⟨t, ht⟩, by simp [ht], htr⟩
  · rintro ⟨⟨t, ht⟩, rfl, htr⟩
    exact ⟨t, by simp [ht], htr⟩

open LTS in
/-- Deleting a parallel transition preserves behaviour: at every marking, the marking graph of `N`
with `t₂` relabelled `t₁` is bisimilar to that of the reduced net. -/
theorem bisimilar [DecidableEq Transition] (M : Marking Place) :
    M ~[N.labelledLts (Function.update id t₂ t₁),
      (N.removeTransition t₂).labelledLts Subtype.val] M := by
  rw [h.labelledLts_removeTransition]

/-- A marking is dead in the reduced net exactly when it is dead in `N`. -/
theorem dead_removeTransition_iff {M : Marking Place} :
    (N.removeTransition t₂).Dead M ↔ N.Dead M := by
  simp only [dead_iff]
  constructor
  · intro hd t
    by_cases ht : t = t₂
    · subst ht
      rw [← h.enabled_iff]
      exact hd ⟨t₁, h.1⟩
    · exact hd ⟨t, ht⟩
  · exact fun hd t => hd t.1

/-- Deleting a parallel transition preserves `k`-boundedness. -/
theorem kBounded_removeTransition_iff {M₀ : Marking Place} {k : ℕ} :
    (N.removeTransition t₂).KBounded M₀ k ↔ N.KBounded M₀ k := by
  simp only [KBounded, h.reachable_removeTransition_iff]

/-- Deleting a parallel transition preserves boundedness. -/
theorem bounded_removeTransition_iff {M₀ : Marking Place} :
    (N.removeTransition t₂).Bounded M₀ ↔ N.Bounded M₀ := by
  simp only [Bounded, h.kBounded_removeTransition_iff]

/-- Deleting a parallel transition preserves safeness. -/
theorem safe_removeTransition_iff {M₀ : Marking Place} :
    (N.removeTransition t₂).Safe M₀ ↔ N.Safe M₀ :=
  h.kBounded_removeTransition_iff

/-- A transition other than the deleted one is live in the reduced net exactly when it is live
in `N`. -/
theorem liveAt_removeTransition_iff {M₀ : Marking Place} (t : {t // t ≠ t₂}) :
    (N.removeTransition t₂).LiveAt M₀ t ↔ N.LiveAt M₀ t.1 := by
  simp only [LiveAt, h.reachable_removeTransition_iff, enabled_removeTransition]

/-- The deleted transition is live exactly when its twin is. -/
theorem liveAt_iff {M₀ : Marking Place} : N.LiveAt M₀ t₁ ↔ N.LiveAt M₀ t₂ := by
  simp only [LiveAt, h.enabled_iff]

/-- A net is live exactly when the net with a parallel transition deleted is live. -/
theorem live_removeTransition_iff {M₀ : Marking Place} :
    (N.removeTransition t₂).Live M₀ ↔ N.Live M₀ := by
  constructor
  · intro hl t
    by_cases ht : t = t₂
    · subst ht
      exact h.liveAt_iff.1 ((h.liveAt_removeTransition_iff ⟨t₁, h.1⟩).1 (hl _))
    · exact (h.liveAt_removeTransition_iff ⟨t, ht⟩).1 (hl _)
  · exact fun hl t => (h.liveAt_removeTransition_iff t).2 (hl _)

end ParallelTransitions

end

end PetriNet

end Cslib
