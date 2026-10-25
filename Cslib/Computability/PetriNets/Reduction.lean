/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.PlaceInvariants
public import Cslib.Computability.PetriNets.RemovePlace
public import Cslib.Computability.PetriNets.Equivalence

/-! # Structural reduction of places

Murata's reduction rules simplify a net while preserving its behaviour. This file treats the rules
that delete a place that never constrains the firing of any transition.

A place `p` is *redundant* at `M₀` if, at every marking reachable from `M₀`, a transition that is
enabled once `p` is deleted is also enabled in the net. Deleting such a place changes neither
the firing sequences nor liveness. A bounded net stays bounded; conversely the reduced net is
bounded exactly when the net is, provided the deleted place is bounded too (which is not automatic).

## Main definitions

- `PetriNet.removePlace`, `PetriNet.Marking.drop`: see `Cslib.Computability.PetriNets.RemovePlace`.
- `PetriNet.RedundantPlace`: the place `p` never blocks a transition at a reachable marking.
- `PetriNet.ParallelPlaces`: two distinct places with the same arcs; decidable for finitely many
  transitions.

## Main statements

- `PetriNet.RedundantPlace.traces_eq`: deleting a redundant place preserves the firing sequences.
- `PetriNet.RedundantPlace.bisimilar`: the initial marking and its restriction are bisimilar. This
  follows from `traces_eq`, as marking graphs are deterministic.
- `PetriNet.RedundantPlace.dead_iff`, `PetriNet.RedundantPlace.live_iff`: deadlocks and liveness
  are preserved.
- `PetriNet.RedundantPlace.bounded_iff`: `N` is bounded iff the reduced net is bounded and the
  deleted place is bounded. In particular `PetriNet.RedundantPlace.bounded_drop`: a bounded net has
  a bounded reduction. The place bound is automatic if no transition adds tokens to the place
  (`PetriNet.RedundantPlace.bounded_iff_of_post_le_pre`).
- `PetriNet.IsIsolated.redundantPlace`: an isolated place is redundant.
- `PetriNet.redundantPlace_of_implicit`: a place whose tokens always cover a weighted sum of the
  tokens elsewhere is redundant (Murata's *implicit place*).
- `PetriNet.redundantPlace_of_selfLoop`: a place that is initially marked enough for every
  transition and that no transition drains is redundant. This generalises Murata's *elimination of
  self-loop places*, which asks for a place that is both input and output of every transition it
  touches, with enough initial tokens.
- `PetriNet.ParallelPlaces.redundantPlace`: of two parallel places, the one with more tokens is
  redundant (*fusion of parallel places*).

Fusion of parallel transitions is in `Cslib.Computability.PetriNets.ReductionTransition`, and
fusion of series transitions and of series places is in
`Cslib.Computability.PetriNets.SeriesReduction` and
`Cslib.Computability.PetriNets.SeriesPlaceReduction`. Elimination of self-loop *transitions* is
in `Cslib.Computability.PetriNets.SelfLoopTransition`.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS

variable {Place : Type*} {Transition : Type*}

/-- Deadlock-freedom from `M₀` is the negation of the reachability of a dead marking, so a
correspondence of reachable dead markings between two nets is one of deadlock-freedom. -/
theorem deadlockFree_congr {Place' : Type*} {Transition' : Type*} {N : PetriNet Place Transition}
    {N' : PetriNet Place' Transition'} {M₀ : Marking Place} {M₀' : Marking Place'}
    (h : (∃ K, M₀ ⇝[N] K ∧ N.Dead K) ↔ ∃ K', M₀' ⇝[N'] K' ∧ N'.Dead K') :
    (∀ K, M₀ ⇝[N] K → ¬ N.Dead K) ↔ ∀ K', M₀' ⇝[N'] K' → ¬ N'.Dead K' := by
  simpa only [not_exists, not_and] using not_congr h

variable [DecidableEq Place]

/-- The place `p` is redundant at `M₀` if at every reachable marking, a transition that is enabled
in the net with `p` deleted is enabled in `N`: the tokens in `p` never block a transition. -/
def RedundantPlace (N : PetriNet Place Transition) (p : Place) (M₀ : Marking Place) : Prop :=
  ∀ M, M₀ ⇝[N] M → ∀ t, (M.drop p) [t⟩[N.removePlace p] → M [t⟩[N]

variable {N : PetriNet Place Transition} {p : Place}

namespace RedundantPlace

variable {M₀ M : Marking Place}

/-- Redundancy passes to reachable markings. -/
theorem of_reachable (h : N.RedundantPlace p M₀) (hM : M₀ ⇝[N] M) : N.RedundantPlace p M :=
  fun _ hM' => h _ (hM.trans hM')

/-- At a reachable marking, `p` holds enough tokens for every transition enabled once `p` is
deleted. -/
theorem count_le (h : N.RedundantPlace p M₀) (hM : M₀ ⇝[N] M) {t : Transition}
    (hen : (M.drop p) [t⟩[N.removePlace p]) : (•[N] t).count p ≤ M.count p :=
  Multiset.count_le_of_le p (h M hM t hen)

/-- Steps of the reduced net from a reachable marking are steps of `N`, up to forgetting `p`. -/
theorem tr_iff (h : N.RedundantPlace p M₀) (hM : M₀ ⇝[N] M) (t : Transition)
    (K : Marking {q // q ≠ p}) :
    (N.removePlace p).lts.Tr (M.drop p) t K ↔ ∃ M', N.lts.Tr M t M' ∧ M'.drop p = K := by
  constructor
  · intro htr
    exact Fires.of_drop (h.count_le hM (enabled_iff_exists_fires.2 ⟨K, htr⟩)) htr
  · rintro ⟨M', htr, rfl⟩
    exact Fires.drop htr

/-- Firing sequences of the reduced net lift to `N`. -/
theorem lift_mTr (h : N.RedundantPlace p M₀) (ts : List Transition) :
    ∀ M, M₀ ⇝[N] M → ∀ K, (N.removePlace p).lts.MTr (M.drop p) ts K →
      ∃ M', N.lts.MTr M ts M' ∧ M'.drop p = K := by
  induction ts with
  | nil =>
    intro M _ K hK
    cases hK
    exact ⟨M, .refl, rfl⟩
  | cons t ts ih =>
    intro M hM K hK
    obtain ⟨K₁, htr, hK₁⟩ := LTS.MTr.cons_iff.1 hK
    obtain ⟨M₁, htr₁, rfl⟩ := (h.tr_iff hM t K₁).1 htr
    obtain ⟨M', hM', rfl⟩ := ih M₁ (hM.trans (Fires.reachable htr₁)) K hK₁
    exact ⟨M', .stepL htr₁ hM', rfl⟩

/-- Reachability in the reduced net is reachability in `N`, up to forgetting `p`. -/
theorem reachable_drop_iff (h : N.RedundantPlace p M₀) (hM : M₀ ⇝[N] M)
    (K : Marking {q // q ≠ p}) :
    (M.drop p) ⇝[N.removePlace p] K ↔ ∃ M', M ⇝[N] M' ∧ M'.drop p = K := by
  constructor
  · rintro ⟨ts, hts⟩
    obtain ⟨M', hM', hK⟩ := h.lift_mTr ts M hM K hts
    exact ⟨M', ⟨ts, hM'⟩, hK⟩
  · rintro ⟨M', hM', rfl⟩
    exact hM'.drop

/-- Deleting a redundant place preserves the firing sequences. -/
theorem traces_eq (h : N.RedundantPlace p M₀) :
    (N.removePlace p).lts.traces (M₀.drop p) = N.lts.traces M₀ := by
  ext ts
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨M', hM', -⟩ := h.lift_mTr ts M₀ (Reachable.refl N M₀) K hK
    exact ⟨M', hM'⟩
  · rintro ⟨M', hM'⟩
    exact ⟨M'.drop p, mTr_drop hM'⟩

/-- Deleting a redundant place preserves the behaviour: the initial marking and its restriction are
bisimilar, as states of the marking graphs of `N` and of the net with `p` deleted. -/
theorem bisimilar (h : N.RedundantPlace p M₀) :
    M₀ ~[N.lts, (N.removePlace p).lts] (M₀.drop p) :=
  (Deterministic.bisimilarity_iff_traceEq M₀ (M₀.drop p)).2 h.traces_eq.symm

/-- A reachable marking is dead exactly when its restriction is dead in the reduced net. -/
theorem dead_iff (h : N.RedundantPlace p M₀) (hM : M₀ ⇝[N] M) :
    N.Dead M ↔ (N.removePlace p).Dead (M.drop p) := by
  simp only [PetriNet.dead_iff]
  exact forall_congr' fun t => not_congr ⟨fun hen => (enabled_iff_drop.1 hen).1, h M hM t⟩

/-- A transition is live in the reduced net exactly when it is live in `N`. -/
theorem liveAt_iff (h : N.RedundantPlace p M₀) (t : Transition) :
    N.LiveAt M₀ t ↔ (N.removePlace p).LiveAt (M₀.drop p) t := by
  constructor
  · intro hl K hK
    obtain ⟨M, hM, rfl⟩ := (h.reachable_drop_iff (Reachable.refl N M₀) K).1 hK
    obtain ⟨M', hM', hen⟩ := hl M hM
    exact ⟨M'.drop p, hM'.drop, (enabled_iff_drop.1 hen).1⟩
  · intro hl M hM
    obtain ⟨K, hK, hen⟩ := hl (M.drop p) hM.drop
    obtain ⟨M', hM', rfl⟩ := ((h.of_reachable hM).reachable_drop_iff (Reachable.refl N M) K).1 hK
    exact ⟨M', hM', h M' (hM.trans hM') t hen⟩

/-- A net is live exactly when the net with a redundant place deleted is live. -/
theorem live_iff (h : N.RedundantPlace p M₀) :
    N.Live M₀ ↔ (N.removePlace p).Live (M₀.drop p) :=
  forall_congr' h.liveAt_iff

/-- `N` is `k`-bounded exactly when the reduced net is `k`-bounded and `p` never exceeds `k`. -/
theorem kBounded_iff (h : N.RedundantPlace p M₀) (k : ℕ) :
    N.KBounded M₀ k ↔
      (N.removePlace p).KBounded (M₀.drop p) k ∧ ∀ M, M₀ ⇝[N] M → M.count p ≤ k := by
  simp only [PetriNet.kBounded_iff]
  constructor
  · intro hk
    refine ⟨fun K hK q => ?_, fun M hM => hk M hM p⟩
    obtain ⟨M, hM, rfl⟩ := (h.reachable_drop_iff (Reachable.refl N M₀) K).1 hK
    simpa using hk M hM q
  · rintro ⟨hk, hp⟩ M hM q
    by_cases hq : q = p
    · subst hq
      exact hp M hM
    · simpa using hk _ hM.drop ⟨q, hq⟩

/-- A net with a redundant place is bounded exactly when the reduced net is bounded and the
redundant place is bounded. -/
theorem bounded_iff (h : N.RedundantPlace p M₀) :
    N.Bounded M₀ ↔
      (N.removePlace p).Bounded (M₀.drop p) ∧ ∃ k, ∀ M, M₀ ⇝[N] M → M.count p ≤ k := by
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨⟨k, ((h.kBounded_iff k).1 hk).1⟩, k, ((h.kBounded_iff k).1 hk).2⟩
  · rintro ⟨⟨k₁, hk₁⟩, k₂, hk₂⟩
    refine ⟨max k₁ k₂, (h.kBounded_iff _).2 ⟨hk₁.mono (le_max_left ..), fun M hM => ?_⟩⟩
    exact (hk₂ M hM).trans (le_max_right ..)

/-- A bounded net has a bounded reduction: deleting a redundant place preserves boundedness. -/
theorem bounded_drop (h : N.RedundantPlace p M₀) (hb : N.Bounded M₀) :
    (N.removePlace p).Bounded (M₀.drop p) :=
  ((h.bounded_iff).1 hb).1

/-- If no transition adds tokens to `p`, the place is bounded by its initial tokens, so `N` is
bounded exactly when the reduced net is. -/
theorem bounded_iff_of_post_le_pre (h : N.RedundantPlace p M₀)
    (hmono : ∀ t, (t •[N]).count p ≤ (•[N] t).count p) :
    N.Bounded M₀ ↔ (N.removePlace p).Bounded (M₀.drop p) := by
  rw [h.bounded_iff]
  refine ⟨fun h => h.1, fun hb => ⟨hb, M₀.count p, fun M hM => ?_⟩⟩
  exact hM.invariant (P := fun K => K.count p ≤ M₀.count p) (fun {M t M'} htr hP => by
    obtain ⟨R, rfl, rfl⟩ := htr
    have := hmono t
    simp only [Multiset.count_add] at hP ⊢
    omega) le_rfl

/-- Safeness of a net with a redundant place is safeness of the reduced net, if the redundant
place is also safe. -/
theorem safe_iff (h : N.RedundantPlace p M₀) :
    N.Safe M₀ ↔ (N.removePlace p).Safe (M₀.drop p) ∧ ∀ M, M₀ ⇝[N] M → M.count p ≤ 1 :=
  h.kBounded_iff 1

end RedundantPlace

/-! ### Sufficient conditions for redundancy -/

/-- *Implicit place.* A place `p` is redundant if its tokens always cover a weighted sum of the
tokens in the other places plus a constant `b`, namely:

* this holds initially (`h₀`), where `w p = 0`,
* it is preserved by every transition (`hstep`), and
* the preset of a transition at `p` is covered whenever the weighted preset elsewhere is (`henab`).
-/
theorem redundantPlace_of_implicit {M₀ : Marking Place} (w : Place → ℕ) (b : ℕ) (hw : w p = 0)
    (h₀ : Marking.weight w M₀ + b ≤ M₀.count p)
    (hstep : ∀ t, (•[N] t).count p + Marking.weight w (t •[N]) ≤
      (t •[N]).count p + Marking.weight w (•[N] t))
    (henab : ∀ t, (•[N] t).count p ≤ Marking.weight w (•[N] t) + b) :
    N.RedundantPlace p M₀ := by
  have inv : ∀ M, M₀ ⇝[N] M → Marking.weight w M + b ≤ M.count p := fun M hM =>
    hM.invariant (P := fun K => Marking.weight w K + b ≤ K.count p) (fun {M t M'} htr hP => by
      obtain ⟨R, rfl, rfl⟩ := htr
      simp only [map_add, Multiset.count_add] at hP ⊢
      have := hstep t
      omega) h₀
  intro M hM t hen
  refine enabled_iff_drop.2 ⟨hen, ?_⟩
  have h1 := inv M hM
  have h2 : Marking.weight w (•[N] t) ≤ Marking.weight w M := by
    refine Marking.weight_le_weight fun q hq => ?_
    have hqp : q ≠ p := fun h => hq (h ▸ hw)
    simpa using Multiset.le_iff_count.1 hen ⟨q, hqp⟩
  have := henab t
  omega

/-- *Elimination of a self-loop place.* A place that is marked enough initially for every
transition, and that no transition drains, is redundant. This generalises Murata's rule, where the
place is an input and an output of every transition that touches it. -/
theorem redundantPlace_of_selfLoop {M₀ : Marking Place}
    (hmark : ∀ t, (•[N] t).count p ≤ M₀.count p)
    (hmono : ∀ t, (•[N] t).count p ≤ (t •[N]).count p) :
    N.RedundantPlace p M₀ :=
  redundantPlace_of_implicit (fun _ => 0) (M₀.count p) rfl
    (by simp [Marking.weight_apply])
    (fun t => by simpa [Marking.weight_apply] using hmono t)
    (fun t => by simpa [Marking.weight_apply] using hmark t)

/-- Two places are *parallel* if they are distinct and every transition consumes and produces as
many tokens in one as in the other. -/
def ParallelPlaces (N : PetriNet Place Transition) (p q : Place) : Prop :=
  p ≠ q ∧ (∀ t, (•[N] t).count p = (•[N] t).count q) ∧ ∀ t, (t •[N]).count p = (t •[N]).count q

instance [Fintype Transition] (N : PetriNet Place Transition) (p q : Place) :
    Decidable (N.ParallelPlaces p q) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

/-- *Fusion of parallel places.* If `p` and `q` are parallel, and `q` initially has at most as many
tokens as `p`, then `p` is redundant: it always keeps at least as many tokens as `q`. -/
theorem ParallelPlaces.redundantPlace {M₀ : Marking Place} {q : Place}
    (h : N.ParallelPlaces p q) (h₀ : M₀.count q ≤ M₀.count p) : N.RedundantPlace p M₀ := by
  obtain ⟨hpq, hpre, hpost⟩ := h
  exact redundantPlace_of_implicit (fun r => if r = q then 1 else 0) 0 (by simp [hpq])
    (by simpa [Marking.weight_ite_eq] using h₀)
    (fun t => by simp [Marking.weight_ite_eq, hpre t, hpost t, Nat.add_comm])
    (fun t => by simp [Marking.weight_ite_eq, hpre t])

/-- An isolated place is redundant: no transition ever needs a token from it. -/
theorem IsIsolated.redundantPlace {M₀ : Marking Place} (h : N.IsIsolated p) :
    N.RedundantPlace p M₀ :=
  fun _ _ _ hen => h.enabled_iff.1 hen

end PetriNet

end Cslib
