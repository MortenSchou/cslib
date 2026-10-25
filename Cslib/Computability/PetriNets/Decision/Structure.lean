/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.FreeChoice
public import Cslib.Computability.PetriNets.PlaceInvariants

/-! # Deciding structural properties of nets

Over finitely many transitions, and with decidable equality on places, the structural properties of
a net are decidable: whether it is conservative, ordinary or free-choice, whether a weighting is an
invariant, and whether a decidable set of places is a siphon or a trap. Over finitely many places,
it is also decidable whether every place has an output transition, and whether the net has the
siphon-trap property. The latter is quantified over all sets of places, and is decided by
quantifying over finite sets instead.

Together with the decision procedures for boundedness, reachability and soundness, this lets
`decide` check the hypotheses of the structural theorems, such as
`PetriNet.live_of_siphons_contain_marked_trap`.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} {N : PetriNet Place Transition}

instance [Fintype Transition] : Decidable N.Conservative :=
  inferInstanceAs (Decidable (∀ _, _ = _))

instance [DecidableEq Place] [Fintype Transition] : Decidable N.Ordinary :=
  inferInstanceAs (Decidable (∀ _, _ ∧ _))

instance [DecidableEq Place] [Fintype Transition] : Decidable N.IsFreeChoice :=
  inferInstanceAs (Decidable (∀ t t', ∀ p ∈ •[N] t, p ∈ •[N] t' → _))

instance [Fintype Transition] {w : Place → ℕ} : Decidable (N.IsInvariant w) :=
  inferInstanceAs (Decidable (∀ _, _ = _))

/-- A siphon: a transition that consumes nothing from the set produces nothing into it. -/
theorem isSiphon_iff {S : Set Place} :
    N.IsSiphon S ↔ ∀ t, (∀ q ∈ •[N] t, q ∉ S) → ∀ p ∈ t •[N], p ∉ S :=
  forall_congr' fun _ => not_imp_not.symm.trans (by simp only [not_exists, not_and, imp_not_comm])

instance [Fintype Transition] {S : Set Place} [DecidablePred (· ∈ S)] :
    Decidable (N.IsSiphon S) :=
  decidable_of_iff _ isSiphon_iff.symm

/-- A trap: a transition that produces nothing into the set consumes nothing from it. -/
theorem isTrap_iff {T : Set Place} :
    N.IsTrap T ↔ ∀ t, (∀ q ∈ t •[N], q ∉ T) → ∀ p ∈ •[N] t, p ∉ T :=
  forall_congr' fun _ => not_imp_not.symm.trans (by simp only [not_exists, not_and, imp_not_comm])

instance [Fintype Transition] {T : Set Place} [DecidablePred (· ∈ T)] :
    Decidable (N.IsTrap T) :=
  decidable_of_iff _ isTrap_iff.symm

theorem markedOn_iff {M : Marking Place} {S : Set Place} : MarkedOn M S ↔ ¬ ∀ p ∈ M, p ∉ S := by
  simp only [MarkedOn]
  grind

instance {M : Marking Place} {S : Set Place} [DecidablePred (· ∈ S)] : Decidable (MarkedOn M S) :=
  decidable_of_iff _ markedOn_iff.symm

/-- The siphon-trap property, quantified over finite sets of places. -/
theorem siphonTrap_iff [Finite Place] {M : Marking Place} :
    N.SiphonTrap M ↔ ∀ S : Finset Place, N.IsSiphon ↑S → S.Nonempty →
      ∃ T ∈ S.powerset, N.IsTrap ↑T ∧ MarkedOn M ↑T := by
  constructor
  · intro h S hS hne
    obtain ⟨T, hTS, hT, hM⟩ := h S hS (Finset.coe_nonempty.2 hne)
    have hT' := (Set.toFinite T).coe_toFinset
    refine ⟨(Set.toFinite T).toFinset, Finset.mem_powerset.2 (Finset.coe_subset.1 ?_), ?_, ?_⟩ <;>
      rwa [hT']
  · intro h S hS hne
    have hS' := (Set.toFinite S).coe_toFinset
    obtain ⟨T, hT, hTr, hM⟩ := h (Set.toFinite S).toFinset (by rwa [hS'])
      (Finset.coe_nonempty.1 (by rwa [hS']))
    refine ⟨T, ?_, hTr, hM⟩
    rw [← hS']
    exact Finset.coe_subset.2 (Finset.mem_powerset.1 hT)

instance [DecidableEq Place] [Fintype Place] [Fintype Transition] {M : Marking Place} :
    Decidable (N.SiphonTrap M) :=
  decidable_of_iff _ siphonTrap_iff.symm

end PetriNet

end Cslib
