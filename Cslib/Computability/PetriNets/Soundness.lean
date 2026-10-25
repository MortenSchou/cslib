/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Unboundedness

/-! # Soundness of workflow nets

A workflow net models a business process: tokens enter at a source place `i` and a case is finished
when a single token sits in a sink place `o`. A net with such a pair of places is *sound* if
every case can be completed, completion leaves no tokens behind, and no transition is dead. By
van der Aalst's theorem, soundness is equivalent to liveness and boundedness of the
*short-circuited* net, obtained by adding a transition from `o` back to `i`.

The usual definition of a workflow net also asks that `i` has no input, `o` has no output and every
node lies on a path from `i` to `o`. The equivalence below does not need these conditions, so it is
proved for arbitrary nets with two designated places.

## Main definitions

- `PetriNet.token`: the marking with a single token in a place.
- `PetriNet.shortCircuit`: the net extended by a transition from `o` to `i`.
- `PetriNet.Sound`: soundness of a net with respect to a source and a sink.

## Main statements

- `PetriNet.sound_iff_live_and_bounded`: a net over finitely many places and transitions is sound
  iff its short-circuited net is live and bounded at `token i`.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition} {i o : Place}

/-- The marking with a single token in the place `p`, that is `{p}`. -/
def token (p : Place) : Marking Place := {p}

/-- A marking contains the single token in `p` iff `p` is marked. -/
theorem token_le_iff {p : Place} {M : Marking Place} : token p ≤ M ↔ p ∈ M :=
  Multiset.singleton_le

/-- The short-circuited net: `N` with an extra transition `none` that moves a token from `o` to
`i`. -/
def shortCircuit (N : PetriNet Place Transition) (i o : Place) :
    PetriNet Place (Option Transition) where
  pre
    | none => token o
    | some t => N.pre t
  post
    | none => token i
    | some t => t •[N]

/-- A net is sound for the source `i` and the sink `o` if, from every marking reachable from a
single token in `i`, the single token in `o` is reachable (option to complete); any reachable
marking that has a token in `o` is exactly that token (proper completion); and every transition
is enabled in some reachable marking (no dead transitions). -/
structure Sound (N : PetriNet Place Transition) (i o : Place) : Prop where
  /-- Every reachable marking can still reach the final marking. -/
  completion : ∀ M, token i ⇝[N] M → M ⇝[N] token o
  /-- A reachable marking with a token in the sink is the final marking. -/
  proper : ∀ M, token i ⇝[N] M → token o ≤ M → M = token o
  /-- Every transition is enabled in some reachable marking. -/
  noDead : ∀ t, ∃ M, token i ⇝[N] M ∧ M [t⟩[N]

theorem mTr_shortCircuit {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : (N.shortCircuit i o).lts.MTr M (ts.map some) M' := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih =>
    exact .stepL (lts := (N.shortCircuit i o).lts)
      (show _ [(some _)⟩[N.shortCircuit i o] _ from htr) ih

theorem Reachable.shortCircuit {M M' : Marking Place} (h : M ⇝[N] M') :
    M ⇝[N.shortCircuit i o] M' :=
  let ⟨_, h⟩ := h
  ⟨_, mTr_shortCircuit h⟩

theorem Fires.shortCircuit_none (R : Marking Place) :
    (token o + R) [none⟩[N.shortCircuit i o] (R + token i) := ⟨R, rfl, rfl⟩

/-- Over a bounded short-circuited net, a reachable marking with a token in the sink is exactly the
final marking: otherwise firing the new transition would give a strictly larger marking than the
initial one. -/
theorem eq_token_of_bounded (hb : (N.shortCircuit i o).Bounded (token i))
    {M : Marking Place} (hM : token i ⇝[N] M) (ho : token o ≤ M) : M = token o := by
  by_contra hne
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 ho
  have hK : K ≠ 0 := fun h => hne (by simp [h])
  have hpos : token i < K + token i := by
    rw [add_comm]; exact lt_add_of_pos_right _ (pos_iff_ne_zero.2 hK)
  exact not_bounded_of_pump (.refl _ _)
    (hM.shortCircuit.trans (Fires.shortCircuit_none K).reachable) hpos hb

/-- If a reachable marking with a token in the sink is always the final marking, then the markings
reachable in the short-circuited net are already reachable in `N`. -/
theorem reachable_of_shortCircuit
    (hp : ∀ M, token i ⇝[N] M → token o ≤ M → M = token o) {M : Marking Place}
    (h : token i ⇝[N.shortCircuit i o] M) : token i ⇝[N] M := by
  refine h.invariant (P := fun K => token i ⇝[N] K) (fun {M u M'} hf hM => ?_) (.refl _ _)
  cases u with
  | some t => exact hM.trans (show M [t⟩[N] M' from hf).reachable
  | none =>
    obtain ⟨R, rfl, rfl⟩ : ∃ R, M = token o + R ∧ M' = R + token i := hf
    have hR : R = 0 := by
      have := hp _ hM le_self_add
      simpa using this
    subst hR
    simpa using Reachable.refl N (token i)

/-- From a marking reachable in `N`, if the short-circuited net reaches a marking with a token in
the sink, then `N` itself reaches the final marking. -/
theorem reachable_token_of_shortCircuit
    (hp : ∀ M, token i ⇝[N] M → token o ≤ M → M = token o) {M M' : Marking Place}
    {ts : List (Option Transition)} (h : (N.shortCircuit i o).lts.MTr M ts M')
    (hM : token i ⇝[N] M) (hle : token o ≤ M') : M ⇝[N] token o := by
  induction h with
  | refl => rw [hp _ hM hle]; exact .refl _ _
  | @stepL M u M₁ ts M' htr _ ih =>
    cases u with
    | none =>
      obtain ⟨R, rfl, -⟩ : ∃ R, M = token o + R ∧ M₁ = R + token i := htr
      rw [hp _ hM le_self_add]; exact .refl _ _
    | some t =>
      have hf : M [t⟩[N] M₁ := htr
      exact hf.reachable.trans (ih (hM.trans hf.reachable) hle)

/-- Liveness and boundedness of the short-circuited net imply soundness. -/
theorem Sound.of_live_of_bounded (hl : (N.shortCircuit i o).Live (token i))
    (hb : (N.shortCircuit i o).Bounded (token i)) : Sound N i o :=
  have hp : ∀ M, token i ⇝[N] M → token o ≤ M → M = token o :=
    fun _ hM ho => eq_token_of_bounded hb hM ho
  { proper := hp
    completion := fun M hM => by
      obtain ⟨M', ⟨ts, hts⟩, hen⟩ := hl none M hM.shortCircuit
      exact reachable_token_of_shortCircuit hp hts hM hen
    noDead := fun t => by
      obtain ⟨M', hM', hen⟩ := hl (some t) (token i) (.refl _ _)
      exact ⟨M', reachable_of_shortCircuit hp hM', hen⟩ }

/-- A sound net over finitely many places and transitions has a bounded short-circuited net. -/
theorem Sound.bounded [Finite Place] [Finite Transition] (hs : Sound N i o) :
    (N.shortCircuit i o).Bounded (token i) := by
  rw [bounded_iff_no_pump]
  rintro ⟨M₁, M₂, h₁, h₂, hlt⟩
  have h₁N := reachable_of_shortCircuit hs.proper h₁
  have h₂N := reachable_of_shortCircuit hs.proper (h₁.trans h₂)
  obtain ⟨K, rfl⟩ := le_iff_exists_add.1 hlt.le
  have hK : K ≠ 0 := by rintro rfl; simp at hlt
  obtain ⟨ts, hσ⟩ := hs.completion M₁ h₁N
  have hr : token i ⇝[N] (token o + K) :=
    h₂N.trans ⟨ts, by simpa [add_comm] using mTr_add hσ K⟩
  have := hs.proper _ hr le_self_add
  exact hK (by simpa using this)

/-- A sound net over finitely many places and transitions is bounded. -/
theorem Sound.bounded_net [Finite Place] [Finite Transition] (hs : Sound N i o) :
    N.Bounded (token i) :=
  let ⟨k, hk⟩ := hs.bounded
  ⟨k, fun _ hM p => hk _ hM.shortCircuit p⟩

/-- A sound net has a live short-circuited net. -/
theorem Sound.live (hs : Sound N i o) : (N.shortCircuit i o).Live (token i) := by
  intro u M hM
  have hMN := reachable_of_shortCircuit hs.proper hM
  have hc : M ⇝[N.shortCircuit i o] token o := (hs.completion M hMN).shortCircuit
  have hback : token o ⇝[N.shortCircuit i o] token i := by
    simpa using (Fires.shortCircuit_none (N := N) (i := i) (o := o) 0).reachable
  cases u with
  | none => exact ⟨token o, hc, le_rfl⟩
  | some t =>
    obtain ⟨M₀, hM₀, hen⟩ := hs.noDead t
    exact ⟨M₀, (hc.trans hback).trans hM₀.shortCircuit, hen⟩

/-- **Van der Aalst's theorem**: a net over finitely many places and transitions is sound iff its
short-circuited net is live and bounded. -/
theorem sound_iff_live_and_bounded [Finite Place] [Finite Transition] :
    Sound N i o ↔ (N.shortCircuit i o).Live (token i) ∧ (N.shortCircuit i o).Bounded (token i) :=
  ⟨fun hs => ⟨hs.live, hs.bounded⟩, fun ⟨hl, hb⟩ => Sound.of_live_of_bounded hl hb⟩

end PetriNet

end Cslib
