/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ReductionTransition
public import Cslib.Computability.PetriNets.SeriesReduction

/-! # Elimination of self-loop transitions

Murata's reduction *elimination of self-loop transitions* deletes a transition `t` whose preset and
postset are equal (`IsSelfLoopTransition`). Such a transition is enabled exactly when its preset is
covered, and firing it does not change the marking. The reduced net is `PetriNet.removeTransition`.

## What is preserved

For every initial marking, with no side condition:

* the reachable markings, hence `k`-boundedness, boundedness and safeness
  (`IsSelfLoopTransition.reachable_removeTransition_iff` and the following results);
* the observable behaviour: each marking is weakly bisimilar to itself in the reduced net, where
  `t` is the invisible action (`IsSelfLoopTransition.weakBisimilar`), hence they have the same weak
  traces;
* every transition other than `t` is live in the reduced net iff it is live in the net
  (`IsSelfLoopTransition.live_removeTransition_iff`);
* a dead marking of the net is dead in the reduced net.

## What is not preserved without a side condition

* *Deadlocks.* A marking at which `t` is enabled and no other transition is, is not dead in the
  net, but is dead in the reduced net. The net can therefore be deadlock-free while the reduced
  net reaches a dead marking. Reachable deadlocks, and deadlock-freedom, correspond if `t` is never
  the only enabled transition at a reachable marking
  (`IsSelfLoopTransition.exists_dead_removeTransition_iff`). This holds for a live net with a
  transition other than `t` (`IsSelfLoopTransition.exists_enabled_other_of_live`).
* *Liveness of `t`.* The reduced net has no transition `t`. It is live iff all the other transitions
  are live in the net, which is liveness of the net if also `t` is live
  (`IsSelfLoopTransition.live_iff_of_liveAt`). A net with a dead self-loop transition has a live
  reduction.
* *Workflow nets and soundness.* The transition `t` can carry the only path from the source to a
  place of its preset, so the reduced net need not be a workflow net. This file makes no claim
  about soundness.

## Main definitions

- `PetriNet.IsSelfLoopTransition`: the transition has equal preset and postset; decidable when
  places have decidable equality.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

variable {Place Transition : Type*} {N : PetriNet Place Transition} {t : Transition}

/-- `t` is a *self-loop transition* if its preset equals its postset, with arbitrary weights. -/
def IsSelfLoopTransition (N : PetriNet Place Transition) (t : Transition) : Prop :=
  •[N] t = t •[N]

instance [DecidableEq Place] (N : PetriNet Place Transition) (t : Transition) :
    Decidable (N.IsSelfLoopTransition t) :=
  inferInstanceAs (Decidable (_ = _))

/-! ### Deadlocks of the net with a transition deleted -/

/-- A dead marking of a net is dead in the net with a transition deleted. -/
theorem dead_removeTransition_of_dead {M : Marking Place} (hd : N.Dead M) :
    (N.removeTransition t).Dead M := by
  rw [dead_iff] at hd ⊢
  exact fun t' => hd t'.1

/-- A marking that is dead in the net with `t` deleted is dead in the net if `t` is not enabled. -/
theorem dead_of_dead_removeTransition {M : Marking Place} (hd : (N.removeTransition t).Dead M)
    (ht : ¬ M [t⟩[N]) : N.Dead M := by
  rw [dead_iff] at hd ⊢
  intro u
  by_cases hu : u = t
  · rwa [hu]
  · exact hd ⟨u, hu⟩

namespace IsSelfLoopTransition

/-- A self-loop transition fires, when it is enabled, without changing the marking. -/
theorem fires_iff (h : N.IsSelfLoopTransition t) {M M' : Marking Place} :
    M [t⟩[N] M' ↔ M [t⟩[N] ∧ M' = M := by
  constructor
  · rintro ⟨R, rfl, rfl⟩
    exact ⟨le_self_add, by rw [← h, add_comm]⟩
  · rintro ⟨he, rfl⟩
    obtain ⟨R, rfl⟩ := le_iff_exists_add.1 he
    exact ⟨R, rfl, by rw [← h, add_comm]⟩

/-- Deleting a self-loop transition does not change the reachable markings. -/
theorem reachable_removeTransition_iff (h : N.IsSelfLoopTransition t) {M M' : Marking Place} :
    (M ⇝[N.removeTransition t] M') ↔ M ⇝[N] M' := by
  refine ⟨reachable_of_reachable_removeTransition, fun hr => ?_⟩
  refine hr.invariant (P := fun K => M ⇝[N.removeTransition t] K) (fun {K u K'} hf hK => ?_)
    (Reachable.refl _ _)
  by_cases hu : u = t
  · subst hu
    rwa [(h.fires_iff.1 hf).2]
  · exact hK.trans (Fires.reachable (N := N.removeTransition t) (t := ⟨u, hu⟩) hf)

/-- Deleting a self-loop transition preserves `k`-boundedness. -/
theorem kBounded_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    {k : ℕ} : (N.removeTransition t).KBounded M₀ k ↔ N.KBounded M₀ k := by
  simp only [KBounded, h.reachable_removeTransition_iff]

/-- Deleting a self-loop transition preserves boundedness. -/
theorem bounded_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place} :
    (N.removeTransition t).Bounded M₀ ↔ N.Bounded M₀ :=
  exists_congr fun _ => h.kBounded_removeTransition_iff

/-- Deleting a self-loop transition preserves safeness. -/
theorem safe_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place} :
    (N.removeTransition t).Safe M₀ ↔ N.Safe M₀ :=
  h.kBounded_removeTransition_iff

/-- Every marking is weakly bisimilar to itself in the net with a self-loop transition deleted,
where `t` is the invisible action. -/
theorem weakBisimilar [DecidableEq Transition] (h : N.IsSelfLoopTransition t) (M : Marking Place) :
    WeakBisimilarity (N.labelledLts (hide t)) ((N.removeTransition t).labelledLts some) M M :=
  weakBisimilar_of_collapse (N' := N.removeTransition t) id (fun _ => .refl) (fun _ => rfl)
    (fun hf => (h.fires_iff.1 hf).2) (fun hf => hf) (fun hf => ⟨_, hf, rfl⟩) M

/-- Every marking has the same weak traces in the net and in the net with a self-loop transition
deleted: the traces of the saturated marking graphs, in which `t` is invisible. -/
theorem traceEq_saturate [DecidableEq Transition] (h : N.IsSelfLoopTransition t)
    (M : Marking Place) :
    M ~tr[(N.labelledLts (hide t)).saturate,
      ((N.removeTransition t).labelledLts some).saturate] M := by
  obtain ⟨r, hr, hb⟩ := h.weakBisimilar M
  exact hb.traceEq hr

/-! ### Deadlocks -/

/-- If the net reaches a dead marking, so does the net with a self-loop transition deleted. -/
theorem exists_dead_removeTransition_of_exists_dead (h : N.IsSelfLoopTransition t)
    {M₀ : Marking Place} (hd : ∃ M, M₀ ⇝[N] M ∧ N.Dead M) :
    ∃ K, M₀ ⇝[N.removeTransition t] K ∧ (N.removeTransition t).Dead K :=
  let ⟨M, hr, hd⟩ := hd
  ⟨M, h.reachable_removeTransition_iff.2 hr, dead_removeTransition_of_dead hd⟩

/-- If the net with a self-loop transition deleted is deadlock-free, so is the net. The converse
fails: see `exists_dead_removeTransition_iff`. -/
theorem deadlockFree_of_deadlockFree_removeTransition (h : N.IsSelfLoopTransition t)
    {M₀ : Marking Place}
    (hd : ∀ K, M₀ ⇝[N.removeTransition t] K → ¬ (N.removeTransition t).Dead K) :
    ∀ M, M₀ ⇝[N] M → ¬ N.Dead M := fun M hr hdM =>
  hd M (h.reachable_removeTransition_iff.2 hr) (dead_removeTransition_of_dead hdM)

/-- The net with a self-loop transition deleted reaches a dead marking iff the net does, provided
`t` is never the only enabled transition at a reachable marking. -/
theorem exists_dead_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (hother : ∀ M, M₀ ⇝[N] M → M [t⟩[N] → ∃ u, u ≠ t ∧ M [u⟩[N]) :
    (∃ K, M₀ ⇝[N.removeTransition t] K ∧ (N.removeTransition t).Dead K) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  refine ⟨fun ⟨K, hr, hd⟩ => ?_, h.exists_dead_removeTransition_of_exists_dead⟩
  have hr' := h.reachable_removeTransition_iff.1 hr
  refine ⟨K, hr', dead_of_dead_removeTransition hd fun ht => ?_⟩
  obtain ⟨u, hu, he⟩ := hother K hr' ht
  exact dead_iff.1 hd ⟨u, hu⟩ he

/-- The net with a self-loop transition deleted is deadlock-free iff the net is, provided `t` is
never the only enabled transition at a reachable marking. -/
theorem deadlockFree_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (hother : ∀ M, M₀ ⇝[N] M → M [t⟩[N] → ∃ u, u ≠ t ∧ M [u⟩[N]) :
    (∀ K, M₀ ⇝[N.removeTransition t] K → ¬ (N.removeTransition t).Dead K) ↔
      ∀ M, M₀ ⇝[N] M → ¬ N.Dead M :=
  deadlockFree_congr (h.exists_dead_removeTransition_iff hother)

/-! ### Liveness -/

/-- A transition other than `t` is live in the net with `t` deleted iff it is live in the net. -/
theorem liveAt_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (u : {u // u ≠ t}) : (N.removeTransition t).LiveAt M₀ u ↔ N.LiveAt M₀ u.1 := by
  simp only [LiveAt, h.reachable_removeTransition_iff, enabled_removeTransition]

/-- The net with a self-loop transition deleted is live iff every other transition is live in the
net. -/
theorem live_removeTransition_iff (h : N.IsSelfLoopTransition t) {M₀ : Marking Place} :
    (N.removeTransition t).Live M₀ ↔ ∀ u, u ≠ t → N.LiveAt M₀ u :=
  ⟨fun hl u hu => (h.liveAt_removeTransition_iff ⟨u, hu⟩).1 (hl _),
    fun hl u => (h.liveAt_removeTransition_iff u).2 (hl _ u.2)⟩

/-- A live net has a live reduction. -/
theorem live_removeTransition (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (hl : N.Live M₀) : (N.removeTransition t).Live M₀ :=
  h.live_removeTransition_iff.2 fun u _ => hl u

/-- If the self-loop transition is live, the net is live iff the net with the transition deleted
is. Without it the reduced net can be live although the net is not. -/
theorem live_iff_of_liveAt (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (ht : N.LiveAt M₀ t) : (N.removeTransition t).Live M₀ ↔ N.Live M₀ := by
  refine ⟨fun hl u => ?_, h.live_removeTransition⟩
  by_cases hu : u = t
  · rwa [hu]
  · exact h.live_removeTransition_iff.1 hl u hu

/-- In a live net with a transition other than `t`, the self-loop transition `t` is never the only
enabled transition at a reachable marking: from such a marking nothing but `t` can fire, and `t`
does not change the marking, so no other transition could ever become enabled. -/
theorem exists_enabled_other_of_live (h : N.IsSelfLoopTransition t) {M₀ : Marking Place}
    (hl : N.Live M₀) (hne : ∃ u, u ≠ t) {M : Marking Place} (hM : M₀ ⇝[N] M) (ht : M [t⟩[N]) :
    ∃ u, u ≠ t ∧ M [u⟩[N] := by
  by_contra hno
  push Not at hno
  obtain ⟨u, hu⟩ := hne
  obtain ⟨M', hr, he⟩ := hl u M hM
  have hMM : M' = M :=
    hr.invariant (P := fun K => K = M) (fun {K v K'} hf hK => by
      subst hK
      by_cases hv : v = t
      · subst hv
        exact (h.fires_iff.1 hf).2
      · exact absurd (enabled_iff_exists_fires.2 ⟨_, hf⟩) (hno v hv)) rfl
  subst hMM
  exact hno u hu he

end IsSelfLoopTransition

end PetriNet

end Cslib
