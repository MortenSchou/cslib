/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableBoundedness

/-! # Reachability and deadlocks of bounded executable nets

A closed level `n` of `ExecPetriNet.reachSet` contains every marking reachable from the initial
one, so reachability questions about such a net become finite queries. Reachability of a marking and
the existence of a reachable dead marking are decidable for bounded nets, since a bounded net has a
closed level, found with `searchNat`.

## Main definitions

- `ExecPetriNet.DeadlockWithin`: a dead marking among the markings reachable within `n` steps.
- `ExecPetriNet.decidableReachable`, `ExecPetriNet.decidableDeadlock`: decision procedures for
  bounded nets.

## Main statements

- `ExecPetriNet.reachable_iff_mem_reachSet`: at a closed level, reachability is membership.
- `ExecPetriNet.deadlock_iff_deadlockWithin`: at a closed level, a dead marking is reachable iff
  one lies in the level.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  (N : ExecPetriNet Place Transition)

/-- A dead marking lies among the markings reachable from `M₀` within `n` steps. -/
def DeadlockWithin (M₀ : Multiset Place) (n : ℕ) : Prop :=
  ∃ M ∈ N.reachSet M₀ n, ∀ t, ¬ N.pre t ≤ M

instance (M₀ : Multiset Place) (n : ℕ) : Decidable (N.DeadlockWithin M₀ n) :=
  inferInstanceAs (Decidable (∃ M ∈ N.reachSet M₀ n, ∀ t, ¬ N.pre t ≤ M))

variable {N}

/-- At a closed level, a marking is reachable iff it lies in the level. -/
theorem reachable_iff_mem_reachSet {M₀ M : Multiset Place} {n : ℕ} (hc : N.Closed M₀ n) :
    M₀ ⇝[N] M ↔
      M ∈ N.reachSet M₀ n :=
  ⟨mem_reachSet_of_reachable N hc, reachable_of_mem_reachSet N⟩

omit [Fintype Transition] in
theorem dead_toFinsupp_iff {M : Multiset Place} :
    N.toPetriNet.Dead M ↔ ∀ t, ¬ N.pre t ≤ M := by
  simp only [dead_iff, enabled_toPetriNet_iff]

/-- At a closed level, a dead marking is reachable iff one lies in the level. -/
theorem deadlock_iff_deadlockWithin {M₀ : Multiset Place} {n : ℕ} (hc : N.Closed M₀ n) :
    (∃ M, M₀ ⇝[N] M ∧ N.toPetriNet.Dead M) ↔
      N.DeadlockWithin M₀ n := by
  constructor
  · rintro ⟨X, hr, hd⟩
    obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective X
    exact ⟨M, mem_reachSet_of_reachable N hc hr, dead_toFinsupp_iff.1 hd⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨Multiset.toFinsupp M, reachable_of_mem_reachSet N hM, dead_toFinsupp_iff.2 hd⟩

/-- At a closed level, no reachable marking is dead iff every marking in the level enables a
transition. -/
theorem deadlockFree_iff {M₀ : Multiset Place} {n : ℕ} (hc : N.Closed M₀ n) :
    (∀ M, M₀ ⇝[N] M → ¬ N.toPetriNet.Dead M) ↔
      ∀ M ∈ N.reachSet M₀ n, ∃ t, N.pre t ≤ M := by
  constructor
  · intro h M hM
    by_contra hcon
    push Not at hcon
    exact h _ (reachable_of_mem_reachSet N hM) (dead_toFinsupp_iff.2 hcon)
  · intro h X hr hd
    obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective X
    obtain ⟨t, ht⟩ := h M (mem_reachSet_of_reachable N hc hr)
    exact dead_toFinsupp_iff.1 hd t ht

variable [Fintype Place]

/-- A closed level of the markings reachable from `M₀`, for a bounded net. -/
def closedLevel (M₀ : Multiset Place) (hb : N.toPetriNet.Bounded M₀) : ℕ :=
  searchNat (N.Closed M₀) (exists_closed N hb)

theorem closed_closedLevel {M₀ : Multiset Place}
    (hb : N.toPetriNet.Bounded M₀) : N.Closed M₀ (N.closedLevel M₀ hb) :=
  searchNat_spec (N.Closed M₀) (exists_closed N hb)

/-- Reachability is decidable for bounded executable nets: find a closed level and look the marking
up. -/
def decidableReachable (M₀ M : Multiset Place)
    (hb : N.toPetriNet.Bounded M₀) :
    Decidable (M₀ ⇝[N] M) :=
  decidable_of_iff (M ∈ N.reachSet M₀ (N.closedLevel M₀ hb))
    (reachable_iff_mem_reachSet (closed_closedLevel hb)).symm

/-- Reachability of a dead marking is decidable for bounded executable nets. -/
def decidableDeadlock (M₀ : Multiset Place)
    (hb : N.toPetriNet.Bounded M₀) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.toPetriNet.Dead M) :=
  decidable_of_iff (N.DeadlockWithin M₀ (N.closedLevel M₀ hb))
    (deadlock_iff_deadlockWithin (closed_closedLevel hb)).symm

/-- A statement about all reachable markings is decidable for bounded executable nets, if it is
decidable at each reachable marking. -/
def decidableForallReachable (M₀ : Multiset Place)
    (hb : N.toPetriNet.Bounded M₀) (P : Multiset Place → Prop)
    (inst : ∀ m : Multiset Place, M₀ ⇝[N] m →
      Decidable (P m)) :
    Decidable (∀ m : Multiset Place, M₀ ⇝[N] m →
      P m) :=
  @decidable_of_iff _ (∀ m ∈ N.reachSet M₀ (N.closedLevel M₀ hb), P m)
    ⟨fun h m hr => h m (mem_reachSet_of_reachable N (closed_closedLevel hb) hr),
      fun h m hm => h m (reachable_of_mem_reachSet N hm)⟩
    (@Finset.decidableDforallFinset _ _ (fun m _ => P m)
      (fun m hm => inst m (reachable_of_mem_reachSet N hm)))

/-- The existence of a reachable marking with a property is decidable for bounded executable nets,
if the property is decidable at each reachable marking. -/
def decidableExistsReachable (M₀ : Multiset Place)
    (hb : N.toPetriNet.Bounded M₀) (P : Multiset Place → Prop)
    (inst : ∀ m : Multiset Place, M₀ ⇝[N] m →
      Decidable (P m)) :
    Decidable (∃ m : Multiset Place, M₀ ⇝[N] m ∧
      P m) :=
  @decidable_of_iff _ (∃ m : Multiset Place, ∃ _ : m ∈ N.reachSet M₀ (N.closedLevel M₀ hb), P m)
    ⟨fun ⟨m, hm, hP⟩ => ⟨m, reachable_of_mem_reachSet N hm, hP⟩,
      fun ⟨m, hr, hP⟩ => ⟨m, mem_reachSet_of_reachable N (closed_closedLevel hb) hr, hP⟩⟩
    (@Finset.decidableDExistsFinset _ _ (fun m _ => P m)
      (fun m hm => inst m (reachable_of_mem_reachSet N hm)))

/-- Reachability is decided by `decide` once boundedness is available as a `Fact`. -/
instance (M₀ M : Multiset Place) [h : Fact (N.toPetriNet.Bounded M₀)] :
    Decidable (M₀ ⇝[N] M) :=
  decidableReachable M₀ M h.out

/-- Deadlock reachability is decided by `decide` once boundedness is available as a `Fact`. -/
instance (M₀ : Multiset Place) [h : Fact (N.toPetriNet.Bounded M₀)] :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.toPetriNet.Dead M) :=
  decidableDeadlock M₀ h.out

end ExecPetriNet

end Cslib
