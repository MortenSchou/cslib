/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Siphons and traps

Structural properties relate the shape of the net to its behaviour. A *siphon* is a set of places
that, once empty, stays empty; a *trap* is a set of places that, once marked, stays marked. In an
*ordinary* net (all arc weights at most `1`), the empty places at a dead marking form a siphon,
which yields a sufficient condition for deadlock-freedom.

## Main definitions

- `PetriNet.IsSiphon`: every transition that produces into the set also consumes from it.
- `PetriNet.IsTrap`: every transition that consumes from the set also produces into it.
- `PetriNet.MarkedOn`: a marking has a token somewhere in a set of places.
- `PetriNet.SiphonTrap`: every nonempty siphon contains a trap marked at the initial marking.
- `PetriNet.Ordinary`: all arc weights are at most `1`, i.e. presets and postsets have no
  duplicates.

## Main statements

- `PetriNet.IsSiphon.unmarked_of_reachable`: an unmarked siphon stays unmarked.
- `PetriNet.IsTrap.marked_of_reachable`: a marked trap stays marked.
- `PetriNet.maxTrap`: the largest trap contained in a set of places.
- `PetriNet.Live.marked_siphon`: live nets keep every nonempty siphon marked.
- `PetriNet.not_dead_of_siphons_contain_marked_trap`: if every nonempty siphon contains a trap
  marked at `M₀`, no dead marking is reachable from `M₀`.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

variable (N) in
/-- A siphon: every transition that produces tokens into the set also consumes from it. -/
def IsSiphon (S : Set Place) : Prop :=
  ∀ t, (∃ p ∈ S, p ∈ t •[N]) → ∃ q ∈ S, q ∈ •[N] t

variable (N) in
/-- A trap: every transition that consumes tokens from the set also produces into it. -/
def IsTrap (T : Set Place) : Prop :=
  ∀ t, (∃ p ∈ T, p ∈ •[N] t) → ∃ q ∈ T, q ∈ t •[N]

/-- A marking has a token in some place of `S`. -/
def MarkedOn (M : Marking Place) (S : Set Place) : Prop :=
  ∃ p ∈ S, p ∈ M

variable (N) in
/-- The siphon-trap property at `M₀`: every nonempty siphon contains a trap marked at `M₀`. -/
def SiphonTrap (M₀ : Marking Place) : Prop :=
  ∀ S : Set Place, N.IsSiphon S → S.Nonempty → ∃ T ⊆ S, N.IsTrap T ∧ MarkedOn M₀ T

variable (N) in
/-- An ordinary net has all arc weights at most `1`: presets and postsets have no duplicates. -/
def Ordinary : Prop :=
  ∀ t, (•[N] t).Nodup ∧ (t •[N]).Nodup

/-- An unmarked siphon stays unmarked after a firing. -/
theorem IsSiphon.unmarked_fires {S : Set Place} (hS : N.IsSiphon S) {M M' : Marking Place}
    {t : Transition} (h : M [t⟩[N] M') (hM : ¬ MarkedOn M S) : ¬ MarkedOn M' S := by
  obtain ⟨R, rfl, rfl⟩ := h
  rintro ⟨p, hp, hpM'⟩
  obtain hpR | hpost := Multiset.mem_add.1 hpM'
  · exact hM ⟨p, hp, Multiset.mem_add.2 (.inr hpR)⟩
  · obtain ⟨q, hq, hqpre⟩ := hS t ⟨p, hp, hpost⟩
    exact hM ⟨q, hq, Multiset.mem_add.2 (.inl hqpre)⟩

/-- An unmarked siphon stays unmarked along every firing sequence. -/
theorem IsSiphon.unmarked_of_reachable {S : Set Place} (hS : N.IsSiphon S) {M M' : Marking Place}
    (h : M ⇝[N] M') (hM : ¬ MarkedOn M S) : ¬ MarkedOn M' S :=
  h.invariant (P := fun K => ¬ MarkedOn K S) (fun htr hK => hS.unmarked_fires htr hK) hM

/-- A marked trap stays marked after a firing. -/
theorem IsTrap.marked_fires {T : Set Place} (hT : N.IsTrap T) {M M' : Marking Place}
    {t : Transition} (h : M [t⟩[N] M') (hM : MarkedOn M T) : MarkedOn M' T := by
  obtain ⟨R, rfl, rfl⟩ := h
  obtain ⟨p, hp, hpM⟩ := hM
  obtain hpre | hpR := Multiset.mem_add.1 hpM
  · obtain ⟨q, hq, hqpost⟩ := hT t ⟨p, hp, hpre⟩
    exact ⟨q, hq, Multiset.mem_add.2 (.inr hqpost)⟩
  · exact ⟨p, hp, Multiset.mem_add.2 (.inl hpR)⟩

/-- A marked trap stays marked along every firing sequence. -/
theorem IsTrap.marked_of_reachable {T : Set Place} (hT : N.IsTrap T) {M M' : Marking Place}
    (h : M ⇝[N] M') (hM : MarkedOn M T) : MarkedOn M' T :=
  h.invariant (P := fun K => MarkedOn K T) (fun htr hK => hT.marked_fires htr hK) hM

/-- **Siphon property of live nets**: if every place has an output transition, a live net keeps
every nonempty siphon marked at every reachable marking. -/
theorem Live.marked_siphon {M₀ M : Marking Place} (hl : N.Live M₀)
    (hout : ∀ p, ∃ t, p ∈ •[N] t) {S : Set Place} (hS : N.IsSiphon S) (hne : S.Nonempty)
    (hr : M₀ ⇝[N] M) : MarkedOn M S := by
  by_contra hun
  obtain ⟨p, hp⟩ := hne
  obtain ⟨t, ht⟩ := hout p
  obtain ⟨M', hM', hen⟩ := hl t M hr
  exact hS.unmarked_of_reachable hM' hun ⟨p, hp, Multiset.mem_of_le hen ht⟩

/-- In a live net, a nonempty siphon that is also a trap is its own marked trap: it is marked at
every reachable marking, in particular at `M₀`. -/
theorem Live.marked_of_isTrap {M₀ : Marking Place} (hl : N.Live M₀)
    (hout : ∀ p, ∃ t, p ∈ •[N] t) {S : Set Place} (hS : N.IsSiphon S) (hT : N.IsTrap S)
    (hne : S.Nonempty) : ∃ T ⊆ S, N.IsTrap T ∧ MarkedOn M₀ T :=
  ⟨S, subset_rfl, hT, hl.marked_siphon hout hS hne (.refl _ _)⟩

/-- The union of all traps contained in `S`: the largest trap in `S`. -/
def maxTrap (N : PetriNet Place Transition) (S : Set Place) : Set Place :=
  {p | ∃ T, N.IsTrap T ∧ T ⊆ S ∧ p ∈ T}

theorem isTrap_maxTrap (S : Set Place) : N.IsTrap (N.maxTrap S) := by
  rintro t ⟨p, ⟨T, hT, hTS, hp⟩, hpos⟩
  obtain ⟨q, hq, hqpos⟩ := hT t ⟨p, hp, hpos⟩
  exact ⟨q, ⟨T, hT, hTS, hq⟩, hqpos⟩

theorem maxTrap_subset (S : Set Place) : N.maxTrap S ⊆ S :=
  fun _ ⟨_, _, hTS, hp⟩ => hTS hp

theorem subset_maxTrap {S T : Set Place} (hT : N.IsTrap T) (hTS : T ⊆ S) : T ⊆ N.maxTrap S :=
  fun _ hp => ⟨T, hT, hTS, hp⟩

/-- A nonempty set `Y` of places outside the largest trap of `S` is not, together with the largest
trap, a trap: some transition consumes from `Y` and produces nothing in the largest trap or `Y`. -/
theorem exists_exit (S : Set Place) {Y : Set Place} (hYS : Y ⊆ S \ N.maxTrap S)
    (hY : Y.Nonempty) :
    ∃ u, ∃ y ∈ Y, y ∈ •[N] u ∧ ∀ s ∈ u •[N], s ∉ N.maxTrap S ∧ s ∉ Y := by
  by_contra hcon
  push Not at hcon
  have htrap : N.IsTrap (N.maxTrap S ∪ Y) := by
    rintro t ⟨p, hp | hp, hpos⟩
    · obtain ⟨q, hq, hqpos⟩ := isTrap_maxTrap S t ⟨p, hp, hpos⟩
      exact ⟨q, Or.inl hq, hqpos⟩
    · obtain ⟨s, hs, hsQY⟩ := hcon t p hp hpos
      by_cases hsQ : s ∈ N.maxTrap S
      · exact ⟨s, Or.inl hsQ, hs⟩
      · exact ⟨s, Or.inr (hsQY hsQ), hs⟩
  have hsub : N.maxTrap S ∪ Y ⊆ S := Set.union_subset (maxTrap_subset S) fun y hy => (hYS hy).1
  obtain ⟨y, hy⟩ := hY
  exact (hYS hy).2 (subset_maxTrap htrap hsub (Or.inr hy))

/-- In an ordinary net, at a dead marking every transition has an input place that is empty. -/
theorem Ordinary.exists_empty_input (hord : N.Ordinary) {M : Marking Place} (hd : N.Dead M)
    (t : Transition) : ∃ q, q ∉ M ∧ q ∈ •[N] t := by
  have hn : ¬ •[N] t ≤ M := dead_iff.1 hd t
  rw [Multiset.le_iff_subset (hord t).1, Multiset.subset_iff] at hn
  push Not at hn
  obtain ⟨q, hq, hqM⟩ := hn
  exact ⟨q, hqM, hq⟩

/-- In an ordinary net, the empty places of a dead marking form a siphon. -/
theorem Ordinary.isSiphon_empty (hord : N.Ordinary) {M : Marking Place} (hd : N.Dead M) :
    N.IsSiphon {p | p ∉ M} := fun t _ =>
  let ⟨q, hq, hpos⟩ := hord.exists_empty_input hd t
  ⟨q, hq, hpos⟩

/-- **Deadlock-freedom from siphons and traps**: in an ordinary net with at least one transition,
if every nonempty siphon contains a trap that is marked at `M₀`, then no dead marking is reachable
from `M₀`. -/
theorem not_dead_of_siphons_contain_marked_trap [Nonempty Transition] (hord : N.Ordinary)
    {M₀ : Marking Place} (hst : N.SiphonTrap M₀) {M : Marking Place} (hr : M₀ ⇝[N] M) :
    ¬ N.Dead M := by
  intro hd
  obtain ⟨t⟩ := ‹Nonempty Transition›
  obtain ⟨q, hq, -⟩ := hord.exists_empty_input hd t
  obtain ⟨T, hTS, hT, hmark⟩ := hst _ (hord.isSiphon_empty hd) ⟨q, hq⟩
  obtain ⟨p, hp, hpM⟩ := hT.marked_of_reachable hr hmark
  exact hTS hp hpM

end PetriNet

end Cslib
