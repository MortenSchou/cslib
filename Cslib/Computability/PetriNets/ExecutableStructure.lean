/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Executable
public import Cslib.Computability.PetriNets.FreeChoice
public import Cslib.Computability.PetriNets.PlaceInvariants

/-! # Deciding structural properties of executable nets

For executable nets over finitely many places and transitions, the structural properties of a net
are decidable: whether it is conservative, ordinary or free-choice, whether a weighting is an
invariant, whether a set of places is a siphon or a trap, and whether it has the siphon-trap
property. The last is quantified over all sets of places, and is decided by quantifying over finite
subsets instead.

Together with the decision procedures for boundedness, reachability and soundness, this lets
`decide` check the hypotheses of the structural theorems, such as
`PetriNet.live_of_siphons_contain_marked_trap`.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet

variable {Place Transition : Type*} [DecidableEq Place] {N : ExecPetriNet Place Transition}

theorem size_toFinsupp (s : Multiset Place) :
    Marking.size (Multiset.toFinsupp s) = Multiset.card s := by
  induction s using Multiset.induction with
  | empty => simp
  | cons a s ih =>
    rw [← Multiset.singleton_add, map_add Multiset.toFinsupp, Marking.size_add, ih,
      Multiset.toFinsupp_singleton]
    simp [add_comm]

theorem conservative_iff : N.toPetriNet.Conservative ↔ ∀ t, Multiset.card (N.pre t) =
    Multiset.card (N.post t) := by
  simp [Conservative, toPetriNet, size_toFinsupp]

instance [Fintype Transition] : Decidable N.toPetriNet.Conservative :=
  decidable_of_iff _ conservative_iff.symm

theorem ordinary_iff : N.toPetriNet.Ordinary ↔
    ∀ t p, (N.pre t).count p ≤ 1 ∧ (N.post t).count p ≤ 1 := by
  simp [Ordinary, toPetriNet, Multiset.toFinsupp_apply]

instance [Fintype Place] [Fintype Transition] : Decidable N.toPetriNet.Ordinary :=
  decidable_of_iff _ ordinary_iff.symm

theorem isFreeChoice_iff : N.toPetriNet.IsFreeChoice ↔ ∀ t t' p, 0 < (N.pre t).count p →
    0 < (N.pre t').count p → N.pre t = N.pre t' := by
  simp only [IsFreeChoice, toPetriNet, Multiset.toFinsupp_apply]
  exact forall₃_congr fun _ _ _ => imp_congr_right fun _ => imp_congr_right fun _ =>
    Multiset.toFinsupp.injective.eq_iff

instance [Fintype Place] [Fintype Transition] : Decidable N.toPetriNet.IsFreeChoice :=
  decidable_of_iff _ isFreeChoice_iff.symm

theorem isInvariant_iff {w : Place → ℕ} :
    N.toPetriNet.IsInvariant w ↔ ∀ t, ((N.pre t).map w).sum = ((N.post t).map w).sum := by
  simp [IsInvariant, toPetriNet, Marking.weight_toFinsupp]

instance [Fintype Transition] {w : Place → ℕ} : Decidable (N.toPetriNet.IsInvariant w) :=
  decidable_of_iff _ isInvariant_iff.symm

theorem isSiphon_iff {S : Set Place} : N.toPetriNet.IsSiphon S ↔ ∀ t,
    (∃ p ∈ S, 0 < (N.post t).count p) → ∃ q ∈ S, 0 < (N.pre t).count q := by
  simp [IsSiphon, toPetriNet, Multiset.toFinsupp_apply]

instance [Fintype Place] [Fintype Transition] {S : Set Place} [DecidablePred (· ∈ S)] :
    Decidable (N.toPetriNet.IsSiphon S) :=
  decidable_of_iff _ isSiphon_iff.symm

theorem isTrap_iff {T : Set Place} : N.toPetriNet.IsTrap T ↔ ∀ t,
    (∃ p ∈ T, 0 < (N.pre t).count p) → ∃ q ∈ T, 0 < (N.post t).count q := by
  simp [IsTrap, toPetriNet, Multiset.toFinsupp_apply]

instance [Fintype Place] [Fintype Transition] {T : Set Place} [DecidablePred (· ∈ T)] :
    Decidable (N.toPetriNet.IsTrap T) :=
  decidable_of_iff _ isTrap_iff.symm

theorem markedOn_iff {m : Multiset Place} {S : Set Place} :
    MarkedOn (Multiset.toFinsupp m) S ↔ ∃ p ∈ S, 0 < m.count p := by
  simp [MarkedOn, Multiset.toFinsupp_apply]

instance [Fintype Place] {m : Multiset Place} {S : Set Place} [DecidablePred (· ∈ S)] :
    Decidable (MarkedOn (Multiset.toFinsupp m) S) :=
  decidable_of_iff _ markedOn_iff.symm

theorem hasOutput_iff : (∀ p, ∃ t, 0 < N.toPetriNet.pre t p) ↔
    ∀ p, ∃ t, p ∈ N.pre t := by
  simp [toPetriNet, Multiset.toFinsupp_apply, Multiset.count_pos]

/-- Whether every place has an output transition is decidable for executable nets. -/
instance [Fintype Place] [Fintype Transition] :
    Decidable (∀ p, ∃ t, 0 < N.toPetriNet.pre t p) :=
  decidable_of_iff _ hasOutput_iff.symm

/-- The siphon-trap property of an executable net, quantified over finite sets of places. -/
theorem siphonTrap_iff [Finite Place] {m : Multiset Place} :
    N.toPetriNet.SiphonTrap m ↔ ∀ S : Finset Place, S.Nonempty →
      (∀ t, (∃ p ∈ S, 0 < (N.post t).count p) → ∃ q ∈ S, 0 < (N.pre t).count q) →
      ∃ T ∈ S.powerset, (∀ t, (∃ p ∈ T, 0 < (N.pre t).count p) →
        ∃ q ∈ T, 0 < (N.post t).count q) ∧ ∃ p ∈ T, 0 < m.count p := by
  classical
  have := Fintype.ofFinite Place
  constructor
  · intro h S hne hS
    obtain ⟨T, hTS, hT, hm⟩ := h (S : Set Place) (isSiphon_iff.2 (by simpa using hS))
      (by simpa using hne)
    refine ⟨T.toFinset, Finset.mem_powerset.2 fun p hp => ?_, ?_, ?_⟩
    · exact hTS (by simpa using hp)
    · simpa [isTrap_iff] using isTrap_iff.1 hT
    · simpa [markedOn_iff] using markedOn_iff.1 hm
  · intro h S hS hne
    let S' : Finset Place := Finset.univ.filter (· ∈ S)
    have hS' : ∀ p, p ∈ S' ↔ p ∈ S := by simp [S']
    obtain ⟨T, hT, hTr, hm⟩ := h S' (by obtain ⟨p, hp⟩ := hne; exact ⟨p, (hS' p).2 hp⟩) (by
      rintro t ⟨p, hp, hpos⟩
      obtain ⟨q, hq, hqpos⟩ := isSiphon_iff.1 hS t ⟨p, (hS' p).1 hp, hpos⟩
      exact ⟨q, (hS' q).2 hq, hqpos⟩)
    refine ⟨(T : Set Place), fun p hp => (hS' p).1 (Finset.mem_powerset.1 hT hp),
      isTrap_iff.2 ?_, markedOn_iff.2 ?_⟩
    · rintro t ⟨p, hp, hpos⟩
      obtain ⟨q, hq, hqpos⟩ := hTr t ⟨p, hp, hpos⟩
      exact ⟨q, hq, hqpos⟩
    · obtain ⟨p, hp, hpos⟩ := hm
      exact ⟨p, hp, hpos⟩

instance [Fintype Place] [Fintype Transition] {m : Multiset Place} :
    Decidable (N.toPetriNet.SiphonTrap m) :=
  decidable_of_iff _ siphonTrap_iff.symm

end ExecPetriNet

end Cslib
