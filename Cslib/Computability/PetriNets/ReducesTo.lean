/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ReductionTransition
public import Cslib.Computability.PetriNets.ReductionTransitionWF
public import Cslib.Computability.PetriNets.Rename
public import Cslib.Computability.PetriNets.SelfLoopTransition
public import Cslib.Computability.PetriNets.SeriesPlaceReduction

/-! # Certificates of reduction

`PetriNet.ReducesTo N M₀ N' M₀'` is a certificate that the net `N'` with initial marking `M₀'` is
obtained from `N` with `M₀` by a sequence of Murata's reductions. The places and the transitions of
the nets change along the sequence (deleting a place or a transition passes to a subtype), so the
relation is heterogeneous. Every question that the reductions preserve can be asked about the
reduced net `N'` instead of `N`.

## Rules

- `ReducesTo.redundantPlace`: delete a redundant place (`RedundantPlace`), provided the place is
  bounded whenever the reduced net is. The derived rules `ReducesTo.selfLoopPlace`,
  `ReducesTo.parallelPlace` and `ReducesTo.isolatedPlace` discharge the two side conditions from
  structural conditions.
- `ReducesTo.removeTransition`: delete one of two parallel transitions.
- `ReducesTo.selfLoopTransition`: delete a self-loop transition (`IsSelfLoopTransition`, Murata's
  elimination of self-loop transitions), provided it is never the only enabled transition at a
  reachable marking, and it is live whenever the reduced net is live. Both side conditions hold
  for a live net with a transition other than `t` (`ReducesTo.selfLoopTransition_of_live`).
- `ReducesTo.fuseDrain`: fuse a place with the transition that drains it and delete the place
  (`fuseDelete`), provided the draining transition produces a token somewhere and some transition
  produces into the place. The derived rules `ReducesTo.fuseSeries` (series of transitions, Murata's
  FST) and `ReducesTo.fuseSeriesPlace` (series of places, Murata's FSP) discharge these conditions.
  The initial marking is collapsed, so the initial marking of `N` is arbitrary.

- `ReducesTo.reindex`, `ReducesWF.reindex`: rename the places and the transitions along bijections
  (`PetriNet.rename`), carrying the initial marking, the source and the sink along. Renaming is not
  a reduction, but it preserves every property, and it lets a chain of reductions stay over flat
  types such as `Fin n` instead of nested subtypes.

## Main statements

For `h : ReducesTo N M₀ N' M₀'`:

- `ReducesTo.bounded_iff`: `N'` is bounded at `M₀'` iff `N` is bounded at `M₀`.
- `ReducesTo.kBounded`: if `N` is `k`-bounded then so is `N'`. The converse does not hold for every
  rule: deleting a redundant place preserves `k`-boundedness of the rest of the net only, so `N`
  can be `k`-bounded only after the deleted place is (an isolated or parallel place with more than
  `k` tokens initially is a counterexample). It does hold for the other rules where the
  statement is available: for fusion of a drained place, given that the draining transition
  produces a token somewhere (`IsDrain.kBounded_fuseDelete_collapse_iff`), and for parallel
  transitions and self-loop transitions.
- `ReducesTo.exists_dead_iff`: a dead marking is reachable in `N'` iff one is reachable in `N`;
  the same holds for deadlock-freedom (`deadlockFree_congr`).
- `ReducesTo.live_iff`: `N'` is live iff `N` is.

For workflow nets `ReducesWF N i o N' i' o'` tracks the source and the sink through the series
fusions and the deletion of parallel transitions (`ReducesWF.removeTransition`), and
`ReducesWF.isWFNet_and_sound` shows that `N'` is a workflow net, and sound iff `N` is. Reductions
of places and the elimination of self-loop transitions are not included there. Soundness of the
net with a redundant place deleted does not imply soundness of the net: a workflow net with a
redundant (implicit) place can be unsound because the place keeps a token at a marking that is
final in the reduced net, whereas the reduced net is a sound workflow net. Deleting a self-loop
transition can destroy the workflow structure.

Reductions of places and of transitions do not reduce the number of reachable markings (they only
shrink the net), whereas fusion of series transitions or of series places does. They can still
enable series fusions: deleting the self-loop lock place of a ring of transitions is what makes
its transitions series-reducible.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

universe u v

/-! ### Redundant places -/

section Redundant

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition} {p : Place}
  {M₀ : Marking Place}

namespace RedundantPlace

/-- A redundant place does not change which dead markings are reachable. -/
theorem exists_dead_iff (h : N.RedundantPlace p M₀) :
    (∃ K, (M₀.drop p) ⇝[N.removePlace p] K ∧ (N.removePlace p).Dead K) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  constructor
  · rintro ⟨K, hK, hd⟩
    obtain ⟨M, hM, rfl⟩ := (h.reachable_drop_iff (Reachable.refl N M₀) K).1 hK
    exact ⟨M, hM, (h.dead_iff hM).2 hd⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨M.drop p, hM.drop, (h.dead_iff hM).1 hd⟩

end RedundantPlace

/-- If no transition adds more tokens to `p` than it consumes, `p` never has more tokens than
initially. -/
theorem apply_le_of_post_le_pre (hmono : ∀ t, (t •[N]) p ≤ (•[N] t) p) {M : Marking Place}
    (hM : M₀ ⇝[N] M) : M p ≤ M₀ p :=
  hM.invariant (P := fun K => K p ≤ M₀ p) (fun {M t M'} htr hP => by
    obtain ⟨R, rfl, rfl⟩ := htr
    have := hmono t
    simp only [Finsupp.add_apply] at hP ⊢
    omega) le_rfl

/-- Of two parallel places, the one with more tokens is bounded if the other is bounded in a
reachable marking: the difference of their tokens is constant. -/
theorem ParallelPlaces.apply_le {q : Place} (h : N.ParallelPlaces p q) {k : ℕ}
    (hk : ∀ M, M₀ ⇝[N] M → M q ≤ k) {M : Marking Place} (hM : M₀ ⇝[N] M) : M p ≤ k + M₀ p := by
  obtain ⟨-, hpre, hpost⟩ := h
  have inv : M p + M₀ q = M q + M₀ p :=
    hM.invariant (P := fun K => K p + M₀ q = K q + M₀ p) (fun {M t M'} htr hP => by
      obtain ⟨R, rfl, rfl⟩ := htr
      have h1 := hpre t
      have h2 := hpost t
      simp only [Finsupp.add_apply] at hP ⊢
      omega) (add_comm _ _)
  have := hk M hM
  omega

end Redundant

/-! ### Fusion of a drained place -/

namespace IsDrain

variable {Place Transition : Type*} {N : PetriNet Place Transition} {t₂ : Transition} {p : Place}

/-- A `k`-bounded net stays `k`-bounded after fusing and deleting `p`, from the collapse of the
initial marking. -/
theorem kBounded_fuseDelete_collapse (h : N.IsDrain t₂ p) {M₀ : Marking Place} {k : ℕ}
    (hk : N.KBounded M₀ k) :
    (N.fuseDelete t₂ p).KBounded ((N.collapse t₂ p M₀).drop p) k := by
  have h1 : N.KBounded (N.collapse t₂ p M₀) k := fun M hM =>
    hk M ((h.reachable_collapse_self M₀).trans hM)
  have h2 := h.kBounded_fuse (h.collapse_apply_self M₀) h1
  rw [fuseDelete_eq]
  exact (((h.isIsolated_fuse.redundantPlace (M₀ := N.collapse t₂ p M₀)).kBounded_iff k).1 h2).1

/-- `k`-boundedness is preserved in both directions by fusing and deleting a drained place, from
the collapse of the initial marking, if `t₂` produces a token somewhere. -/
theorem kBounded_fuseDelete_collapse_iff (h : N.IsDrain t₂ p) {M₀ : Marking Place} {k : ℕ}
    (hpost : ∃ q, 0 < (t₂ •[N]) q) :
    (N.fuseDelete t₂ p).KBounded ((N.collapse t₂ p M₀).drop p) k ↔ N.KBounded M₀ k := by
  have h0 := h.collapse_apply_self M₀
  have hr := (h.isIsolated_fuse.redundantPlace (M₀ := N.collapse t₂ p M₀)).kBounded_iff k
  have hp : ∀ M, N.collapse t₂ p M₀ ⇝[N.fuse t₂ p] M → M p ≤ k := fun M hM =>
    (apply_le_of_post_le_pre (fun t => by
      rw [(h.isIsolated_fuse t).2]; exact Nat.zero_le _) hM).trans
      (h0.le.trans (Nat.zero_le _))
  rw [← h.kBounded_collapse_iff hpost, fuseDelete_eq]
  exact ⟨fun hk => h.kBounded_of_fuse h0 hpost (hr.2 ⟨hk, hp⟩),
    fun hk => (hr.1 (h.kBounded_fuse h0 hk)).1⟩

end IsDrain

/-! ### The certificate -/

/-- `ReducesTo N M₀ N' M₀'` says that `N'` with `M₀'` is obtained from `N` with `M₀` by Murata's
reductions. Each rule carries the side conditions that make the reduction preserve boundedness,
reachable deadlocks and liveness, so that these transfer along the certificate. -/
inductive ReducesTo : {Place : Type u} → {Transition : Type v} → {Place' : Type u} →
    {Transition' : Type v} →
    PetriNet Place Transition → Marking Place → PetriNet Place' Transition' → Marking Place' →
    Prop
  /-- The empty reduction. -/
  | refl {Place : Type u} {Transition : Type v} (N : PetriNet Place Transition)
      (M₀ : Marking Place) : ReducesTo N M₀ N M₀
  /-- Reductions compose. -/
  | trans {Place₀ Place₁ Place₂ : Type u} {Transition₀ Transition₁ Transition₂ : Type v}
      {N₀ : PetriNet Place₀ Transition₀} {M₀ : Marking Place₀}
      {N₁ : PetriNet Place₁ Transition₁} {M₁ : Marking Place₁}
      {N₂ : PetriNet Place₂ Transition₂} {M₂ : Marking Place₂} :
      ReducesTo N₀ M₀ N₁ M₁ → ReducesTo N₁ M₁ N₂ M₂ → ReducesTo N₀ M₀ N₂ M₂
  /-- Rename the places and the transitions along bijections. -/
  | reindex {Place Place' : Type u} {Transition Transition' : Type v}
      {N : PetriNet Place Transition} {M₀ : Marking Place} (e : Place ≃ Place')
      (f : Transition ≃ Transition') :
      ReducesTo N M₀ (N.rename e f) (Marking.rename e M₀)
  /-- Delete a redundant place, if it is bounded whenever the reduced net is. -/
  | redundantPlace {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {M₀ : Marking Place} (p : Place) (hr : N.RedundantPlace p M₀)
      (hb : (N.removePlace p).Bounded (M₀.drop p) → ∃ k, ∀ M, M₀ ⇝[N] M → M p ≤ k) :
      ReducesTo N M₀ (N.removePlace p) (M₀.drop p)
  /-- Delete one of two parallel transitions. -/
  | removeTransition {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {M₀ : Marking Place} {t₁ t₂ : Transition} (h : N.ParallelTransitions t₁ t₂) :
      ReducesTo N M₀ (N.removeTransition t₂) M₀
  /-- Delete a self-loop transition, if it is never the only enabled transition at a reachable
  marking, and it is live whenever the reduced net is live. -/
  | selfLoopTransition {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {M₀ : Marking Place} {t : Transition} (h : N.IsSelfLoopTransition t)
      (hd : ∀ M, M₀ ⇝[N] M → M [t⟩[N] → ∃ u, u ≠ t ∧ M [u⟩[N])
      (hl : (N.removeTransition t).Live M₀ → N.LiveAt M₀ t) :
      ReducesTo N M₀ (N.removeTransition t) M₀
  /-- Fuse a place with the transition that drains it, and delete the place. -/
  | fuseDrain {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {M₀ : Marking Place} {t₂ : Transition} {p : Place} (h : N.IsDrain t₂ p)
      (hpost : ∃ q, 0 < (t₂ •[N]) q) (hprod : ∃ t₁, 0 < (t₁ •[N]) p) :
      ReducesTo N M₀ (N.fuseDelete t₂ p) ((N.collapse t₂ p M₀).drop p)

namespace ReducesTo

section Rules

variable {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
  {M₀ : Marking Place}

/-- Delete a self-loop place: it is initially marked enough for every transition, and every
transition consumes as many tokens from it as it produces. -/
theorem selfLoopPlace (p : Place) (hmark : ∀ t, (•[N] t) p ≤ M₀ p)
    (hloop : ∀ t, (t •[N]) p = (•[N] t) p) :
    ReducesTo N M₀ (N.removePlace p) (M₀.drop p) :=
  .redundantPlace p (redundantPlace_of_selfLoop hmark fun t => (hloop t).ge) fun _ =>
    ⟨M₀ p, fun _ hM => apply_le_of_post_le_pre (fun t => (hloop t).le) hM⟩

/-- Delete a place that is parallel to a place `q` that has no more tokens initially. -/
theorem parallelPlace {p q : Place} (h : N.ParallelPlaces p q) (h₀ : M₀ q ≤ M₀ p) :
    ReducesTo N M₀ (N.removePlace p) (M₀.drop p) :=
  .redundantPlace p (h.redundantPlace h₀) fun ⟨k, hk⟩ =>
    ⟨k + M₀ p, fun _ hM => h.apply_le (fun M hM => by simpa using hk _ hM.drop ⟨q, h.1.symm⟩) hM⟩

/-- Delete an isolated place. -/
theorem isolatedPlace {p : Place} (h : N.IsIsolated p) :
    ReducesTo N M₀ (N.removePlace p) (M₀.drop p) :=
  .redundantPlace p h.redundantPlace fun _ =>
    ⟨M₀ p, fun _ hM => apply_le_of_post_le_pre (fun t => by rw [(h t).1, (h t).2]) hM⟩

/-- Delete a self-loop transition of a live net that has a transition other than `t`. -/
theorem selfLoopTransition_of_live {t : Transition} (h : N.IsSelfLoopTransition t)
    (hl : N.Live M₀) (hne : ∃ u, u ≠ t) :
    ReducesTo N M₀ (N.removeTransition t) M₀ :=
  .selfLoopTransition h (fun _ hM ht => h.exists_enabled_other_of_live hl hne hM ht)
    fun _ => hl t

/-- Delete a self-loop transition `t` that has a twin `u` with the same preset: `u` is enabled
whenever `t` is, and `t` is live whenever `u` is. These are checkable side conditions, which do not
need the net to be live. -/
theorem selfLoopTransition_of_twin {t u : Transition} (h : N.IsSelfLoopTransition t) (hu : u ≠ t)
    (hpre : •[N] u = •[N] t) : ReducesTo N M₀ (N.removeTransition t) M₀ :=
  .selfLoopTransition h (fun _ _ ht => ⟨u, hu, by simpa only [Enabled, hpre] using ht⟩)
    fun hl M hM =>
      let ⟨K, hK, he⟩ := (h.liveAt_removeTransition_iff ⟨u, hu⟩).1 (hl ⟨u, hu⟩) M hM
      ⟨K, hK, by simpa only [Enabled, hpre] using he⟩

/-- Fusion of series transitions (Murata's FST): `t₁ → p → t₂`, followed by the deletion of `p`. The
transition `t₂` has to produce a token somewhere, which it does in every workflow net. -/
theorem fuseSeries {t₁ t₂ : Transition} {p : Place} (h : N.IsSeries t₁ t₂ p)
    (hpost : ∃ q, 0 < (t₂ •[N]) q) :
    ReducesTo N M₀ (N.fuseDelete t₂ p) ((N.collapse t₂ p M₀).drop p) :=
  .fuseDrain h.toIsDrain hpost ⟨t₁, h.post_pos⟩

/-- Fusion of series places (Murata's FSP): `p₁ → t → p₂`, followed by the deletion of `p₁`. Some
transition has to produce into `p₁`, otherwise the transition `t` is dead. -/
theorem fuseSeriesPlace {t : Transition} {p₁ p₂ : Place} (h : N.IsSeriesPlace t p₁ p₂)
    (hprod : ∃ t₁, 0 < (t₁ •[N]) p₁) :
    ReducesTo N M₀ (N.fuseDelete t p₁) ((N.collapse t p₁ M₀).drop p₁) :=
  .fuseDrain h.toIsDrain h.post_pos hprod

end Rules

/-- What a certificate transfers from the original net to the reduced net: boundedness,
`k`-boundedness, the reachability of a dead marking, and liveness. Every rule of `ReducesTo`
establishes it, and it is closed under composition, so the four consequences are proved by a single
induction (`ReducesTo.preserves`). -/
structure Preserves {Place Place' : Type*} {Transition Transition' : Type*}
    (N : PetriNet Place Transition) (M₀ : Marking Place) (N' : PetriNet Place' Transition')
    (M₀' : Marking Place') : Prop where
  /-- The reduced net is bounded iff the original net is. -/
  bounded_iff : N'.Bounded M₀' ↔ N.Bounded M₀
  /-- A `k`-bounded net reduces to a `k`-bounded net. -/
  kBounded : ∀ {k : ℕ}, N.KBounded M₀ k → N'.KBounded M₀' k
  /-- A dead marking is reachable in the reduced net iff one is reachable in the original net. -/
  exists_dead_iff : (∃ K, M₀' ⇝[N'] K ∧ N'.Dead K) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M
  /-- The reduced net is live iff the original net is. -/
  live_iff : N'.Live M₀' ↔ N.Live M₀

namespace Preserves

/-- The empty reduction preserves everything. -/
protected theorem refl {Place Transition : Type*} (N : PetriNet Place Transition)
    (M₀ : Marking Place) : Preserves N M₀ N M₀ :=
  ⟨Iff.rfl, id, Iff.rfl, Iff.rfl⟩

/-- Preservation composes. -/
protected theorem trans {Place₀ Place₁ Place₂ Transition₀ Transition₁ Transition₂ : Type*}
    {N₀ : PetriNet Place₀ Transition₀} {M₀ : Marking Place₀}
    {N₁ : PetriNet Place₁ Transition₁} {M₁ : Marking Place₁}
    {N₂ : PetriNet Place₂ Transition₂} {M₂ : Marking Place₂}
    (h₁ : Preserves N₀ M₀ N₁ M₁) (h₂ : Preserves N₁ M₁ N₂ M₂) : Preserves N₀ M₀ N₂ M₂ :=
  ⟨h₂.bounded_iff.trans h₁.bounded_iff, h₂.kBounded ∘ h₁.kBounded,
    h₂.exists_dead_iff.trans h₁.exists_dead_iff, h₂.live_iff.trans h₁.live_iff⟩

end Preserves

/-- Every certificate preserves boundedness, `k`-boundedness, reachable deadlocks and liveness. -/
theorem preserves {Place Place' : Type u} {Transition Transition' : Type v}
    {N : PetriNet Place Transition} {M₀ : Marking Place}
    {N' : PetriNet Place' Transition'} {M₀' : Marking Place'}
    (h : ReducesTo N M₀ N' M₀') : Preserves N M₀ N' M₀' := by
  induction h with
  | refl => exact .refl _ _
  | trans _ _ ih₁ ih₂ => exact ih₁.trans ih₂
  | reindex e f =>
    exact ⟨bounded_rename_iff e f, fun hk => (kBounded_rename_iff e f).2 hk,
      exists_dead_rename_iff e f, live_rename_iff e f⟩
  | redundantPlace p hr hb =>
    exact ⟨⟨fun hN' => (hr.bounded_iff).2 ⟨hN', hb hN'⟩, fun hN => (hr.bounded_iff).1 hN |>.1⟩,
      fun hk => ((hr.kBounded_iff _).1 hk).1, hr.exists_dead_iff, hr.live_iff.symm⟩
  | removeTransition h =>
    exact ⟨h.bounded_removeTransition_iff, fun hk => h.kBounded_removeTransition_iff.2 hk,
      by simp only [h.reachable_removeTransition_iff, h.dead_removeTransition_iff],
      h.live_removeTransition_iff⟩
  | selfLoopTransition h hd hl =>
    exact ⟨h.bounded_removeTransition_iff, fun hk => h.kBounded_removeTransition_iff.2 hk,
      h.exists_dead_removeTransition_iff hd,
      ⟨fun hl' => (h.live_iff_of_liveAt (hl hl')).1 hl', h.live_removeTransition⟩⟩
  | fuseDrain h hpost hprod =>
    exact ⟨h.bounded_fuseDelete_collapse_iff hpost, fun hk => h.kBounded_fuseDelete_collapse hk,
      h.exists_dead_fuseDelete_collapse_iff, h.live_fuseDelete_collapse_iff hprod⟩

variable {Place Place' : Type u} {Transition Transition' : Type v}
  {N : PetriNet Place Transition} {M₀ : Marking Place}
  {N' : PetriNet Place' Transition'} {M₀' : Marking Place'}

/-- Boundedness of the reduced net is boundedness of the original net. -/
theorem bounded_iff (h : ReducesTo N M₀ N' M₀') : N'.Bounded M₀' ↔ N.Bounded M₀ :=
  h.preserves.bounded_iff

/-- A `k`-bounded net reduces to a `k`-bounded net. -/
theorem kBounded (h : ReducesTo N M₀ N' M₀') {k : ℕ} (hk : N.KBounded M₀ k) :
    N'.KBounded M₀' k :=
  h.preserves.kBounded hk

/-- A dead marking is reachable in the reduced net iff one is reachable in the original net. -/
theorem exists_dead_iff (h : ReducesTo N M₀ N' M₀') :
    (∃ K, M₀' ⇝[N'] K ∧ N'.Dead K) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M :=
  h.preserves.exists_dead_iff

/-- The reduced net is live iff the original net is. -/
theorem live_iff (h : ReducesTo N M₀ N' M₀') : N'.Live M₀' ↔ N.Live M₀ :=
  h.preserves.live_iff

end ReducesTo

/-! ### Workflow nets -/

/-- `ReducesWF N i o N' i' o'` says that the workflow net `N'` with source `i'` and sink `o'` is
obtained from `N` with source `i` and sink `o` by fusing series and deleting the drained places,
and by deleting parallel transitions. The source and the sink must not be the deleted place. -/
inductive ReducesWF : {Place : Type u} → {Transition : Type v} → {Place' : Type u} →
    {Transition' : Type v} →
    PetriNet Place Transition → Place → Place → PetriNet Place' Transition' → Place' → Place' →
    Prop
  /-- The empty reduction. -/
  | refl {Place : Type u} {Transition : Type v} (N : PetriNet Place Transition) (i o : Place) :
      ReducesWF N i o N i o
  /-- Reductions compose. -/
  | trans {Place₀ Place₁ Place₂ : Type u} {Transition₀ Transition₁ Transition₂ : Type v}
      {N₀ : PetriNet Place₀ Transition₀} {i₀ o₀ : Place₀}
      {N₁ : PetriNet Place₁ Transition₁} {i₁ o₁ : Place₁}
      {N₂ : PetriNet Place₂ Transition₂} {i₂ o₂ : Place₂} :
      ReducesWF N₀ i₀ o₀ N₁ i₁ o₁ → ReducesWF N₁ i₁ o₁ N₂ i₂ o₂ → ReducesWF N₀ i₀ o₀ N₂ i₂ o₂
  /-- Rename the places and the transitions along bijections, and the source and the sink with
  them. -/
  | reindex {Place Place' : Type u} {Transition Transition' : Type v}
      {N : PetriNet Place Transition} {i o : Place} (e : Place ≃ Place')
      (f : Transition ≃ Transition') : ReducesWF N i o (N.rename e f) (e i) (e o)
  /-- Delete one of two parallel transitions. -/
  | removeTransition {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {t₁ t₂ : Transition} {i o : Place} (h : N.ParallelTransitions t₁ t₂) :
      ReducesWF N i o (N.removeTransition t₂) i o
  /-- Fuse a place with the transition that drains it, and delete the place. -/
  | fuseDrain {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
      {t₂ : Transition} {p i o : Place} (h : N.IsDrain t₂ p) (hi : i ≠ p) (ho : o ≠ p) :
      ReducesWF N i o (N.fuseDelete t₂ p) ⟨i, hi⟩ ⟨o, ho⟩

namespace ReducesWF

/-- Fusion of series transitions (Murata's FST) on a workflow net. -/
theorem fuseSeries {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
    {t₁ t₂ : Transition} {p i o : Place} (h : N.IsSeries t₁ t₂ p) (hi : i ≠ p) (ho : o ≠ p) :
    ReducesWF N i o (N.fuseDelete t₂ p) ⟨i, hi⟩ ⟨o, ho⟩ :=
  .fuseDrain h.toIsDrain hi ho

/-- Fusion of series places (Murata's FSP) on a workflow net. -/
theorem fuseSeriesPlace {Place : Type u} {Transition : Type v} {N : PetriNet Place Transition}
    {t : Transition} {p₁ p₂ i o : Place} (h : N.IsSeriesPlace t p₁ p₂) (hi : i ≠ p₁)
    (ho : o ≠ p₁) : ReducesWF N i o (N.fuseDelete t p₁) ⟨i, hi⟩ ⟨o, ho⟩ :=
  .fuseDrain h.toIsDrain hi ho

/-- Along a certificate, the reduced net is a workflow net, and it is sound iff the original net is
sound. -/
theorem isWFNet_and_sound {Place Place' : Type u} {Transition Transition' : Type v}
    {N : PetriNet Place Transition} {i o : Place}
    {N' : PetriNet Place' Transition'} {i' o' : Place'}
    (h : ReducesWF N i o N' i' o') (hN : N.IsWFNet i o) :
    N'.IsWFNet i' o' ∧ (N'.Sound i' o' ↔ N.Sound i o) := by
  induction h with
  | refl => exact ⟨hN, Iff.rfl⟩
  | trans h₁ _ ih₁ ih₂ =>
    obtain ⟨hN₁, hs₁⟩ := ih₁ hN
    obtain ⟨hN₂, hs₂⟩ := ih₂ hN₁
    exact ⟨hN₂, hs₂.trans hs₁⟩
  | reindex e f => exact ⟨(isWFNet_rename_iff e f).2 hN, sound_rename_iff e f⟩
  | removeTransition h => exact ⟨h.isWFNet_removeTransition_iff.2 hN, h.sound_removeTransition_iff⟩
  | fuseDrain h hi ho =>
    exact ⟨h.isWFNet_fuseDelete hN hi ho,
      h.sound_fuseDelete_iff hi ho (hN.exists_post _) (hN.exists_producer hi.symm)⟩

end ReducesWF

end PetriNet

end Cslib
