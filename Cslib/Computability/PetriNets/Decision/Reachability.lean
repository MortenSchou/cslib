/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.Boundedness

/-! # Reachability and deadlocks of bounded nets

A closed level `n` of `PetriNet.reachSet` contains every marking reachable from the initial one, so
reachability questions about such a net become finite queries. Reachability of a marking and the
existence of a reachable dead marking are decidable for bounded nets, since a bounded net has a
closed level, found with `searchNat`.

## Main definitions

- `PetriNet.DeadlockWithin`: a dead marking among the markings reachable within `n` steps.
- `PetriNet.decidableReachable`, `PetriNet.decidableDeadlock`: decision procedures for bounded
  nets.

## Main statements

- `PetriNet.reachable_iff_mem_reachSet`: at a closed level, reachability is membership.
- `PetriNet.deadlock_iff_deadlockWithin`: at a closed level, a dead marking is reachable iff one
  lies in the level.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  (N : PetriNet Place Transition)

/-- A dead marking lies among the markings reachable from `M₀` within `n` steps. -/
def DeadlockWithin (M₀ : Marking Place) (n : ℕ) : Prop :=
  ∃ M ∈ N.reachSet M₀ n, ∀ t, ¬ M [t⟩[N]

instance (M₀ : Marking Place) (n : ℕ) : Decidable (N.DeadlockWithin M₀ n) :=
  inferInstanceAs (Decidable (∃ M ∈ N.reachSet M₀ n, ∀ t, ¬ M [t⟩[N]))

variable {N}

/-- At a closed level, a marking is reachable iff it lies in the level. -/
theorem reachable_iff_mem_reachSet {M₀ M : Marking Place} {n : ℕ} (hc : N.Closed M₀ n) :
    M₀ ⇝[N] M ↔ M ∈ N.reachSet M₀ n :=
  ⟨mem_reachSet_of_reachable N hc, reachable_of_mem_reachSet N⟩

/-- At a closed level, a dead marking is reachable iff one lies in the level. -/
theorem deadlock_iff_deadlockWithin {M₀ : Marking Place} {n : ℕ} (hc : N.Closed M₀ n) :
    (∃ M, M₀ ⇝[N] M ∧ N.Dead M) ↔ N.DeadlockWithin M₀ n := by
  simp only [DeadlockWithin, dead_iff, reachable_iff_mem_reachSet hc]

/-- At a closed level, no reachable marking is dead iff every marking in the level enables a
transition. -/
theorem deadlockFree_iff {M₀ : Marking Place} {n : ℕ} (hc : N.Closed M₀ n) :
    (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) ↔ ∀ M ∈ N.reachSet M₀ n, ∃ t, M [t⟩[N] := by
  simp only [dead_iff, reachable_iff_mem_reachSet hc, not_forall, not_not]

variable [Fintype Place]

/-- A closed level of the markings reachable from `M₀`, for a bounded net. -/
def closedLevel (M₀ : Marking Place) (hb : N.Bounded M₀) : ℕ :=
  searchNat (N.Closed M₀) (exists_closed N hb)

theorem closed_closedLevel {M₀ : Marking Place} (hb : N.Bounded M₀) :
    N.Closed M₀ (N.closedLevel M₀ hb) :=
  searchNat_spec (N.Closed M₀) (exists_closed N hb)

/-- Reachability is decidable for bounded nets: find a closed level and look the marking up. -/
def decidableReachable (M₀ M : Marking Place) (hb : N.Bounded M₀) : Decidable (M₀ ⇝[N] M) :=
  decidable_of_iff (M ∈ N.reachSet M₀ (N.closedLevel M₀ hb))
    (reachable_iff_mem_reachSet (closed_closedLevel hb)).symm

/-- Reachability of a dead marking is decidable for bounded nets. -/
def decidableDeadlock (M₀ : Marking Place) (hb : N.Bounded M₀) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidable_of_iff (N.DeadlockWithin M₀ (N.closedLevel M₀ hb))
    (deadlock_iff_deadlockWithin (closed_closedLevel hb)).symm

/-- A statement about all reachable markings is decidable for bounded nets, if it is decidable at
each reachable marking. -/
def decidableForallReachable (M₀ : Marking Place) (hb : N.Bounded M₀) (P : Marking Place → Prop)
    (inst : ∀ M, M₀ ⇝[N] M → Decidable (P M)) : Decidable (∀ M, M₀ ⇝[N] M → P M) :=
  @decidable_of_iff _ (∀ M ∈ N.reachSet M₀ (N.closedLevel M₀ hb), P M)
    ⟨fun h M hr => h M (mem_reachSet_of_reachable N (closed_closedLevel hb) hr),
      fun h M hM => h M (reachable_of_mem_reachSet N hM)⟩
    (@Finset.decidableDforallFinset _ _ (fun M _ => P M)
      (fun M hM => inst M (reachable_of_mem_reachSet N hM)))

/-- The existence of a reachable marking with a property is decidable for bounded nets, if the
property is decidable at each reachable marking. -/
def decidableExistsReachable (M₀ : Marking Place) (hb : N.Bounded M₀) (P : Marking Place → Prop)
    (inst : ∀ M, M₀ ⇝[N] M → Decidable (P M)) : Decidable (∃ M, M₀ ⇝[N] M ∧ P M) :=
  @decidable_of_iff _ (∃ M, ∃ _ : M ∈ N.reachSet M₀ (N.closedLevel M₀ hb), P M)
    ⟨fun ⟨M, hM, hP⟩ => ⟨M, reachable_of_mem_reachSet N hM, hP⟩,
      fun ⟨M, hr, hP⟩ => ⟨M, mem_reachSet_of_reachable N (closed_closedLevel hb) hr, hP⟩⟩
    (@Finset.decidableDExistsFinset _ _ (fun M _ => P M)
      (fun M hM => inst M (reachable_of_mem_reachSet N hM)))

/-- Reachability is decided by `decide` once boundedness is available as a `Fact`. -/
instance (M₀ M : Marking Place) [h : Fact (N.Bounded M₀)] : Decidable (M₀ ⇝[N] M) :=
  decidableReachable M₀ M h.out

/-- Deadlock reachability is decided by `decide` once boundedness is available as a `Fact`. -/
instance (M₀ : Marking Place) [h : Fact (N.Bounded M₀)] :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidableDeadlock M₀ h.out

end PetriNet

end Cslib
