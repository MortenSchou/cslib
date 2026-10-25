/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.AutoReduction
public import Cslib.Computability.PetriNets.Decision.Stubborn

/-! # Deadlocks through a reduction and stubborn sets

Two reductions of the state space of a net can be composed.

* A *structural reduction* (`PetriNet.ReducesTo`) replaces the net `N` by a smaller net `N'`:
  fewer places and transitions, and, for series fusions, fewer reachable markings. It preserves
  the reachability of a dead marking (`PetriNet.ReducesTo.exists_dead_iff`).
* A *partial-order reduction* by stubborn sets (`PetriNet.stubbornFinset`) explores only the
  firings of a computed stubborn set at each marking. It preserves the reachability of a dead
  marking (`PetriNet.canReach_dead_iff_reduced_stubbornFinset`), without any assumption on the net.

Applied one after the other, a dead marking is reachable in `N` if and only if the stubborn-reduced
graph of `N'` reaches a dead marking. This is decided by computing the reduced reachable markings
of `N'`, `PetriNet.reducedReachSet`, up to a *closed* level, `PetriNet.ReducedClosed`: the
structural reduction removes the sequences of series transitions, and the stubborn sets remove the
interleavings of the independent parts that remain.

Only deadlocks are preserved by both. Liveness and boundedness are preserved by the structural
reduction but not by stubborn sets, which may omit the firings that are needed for them, and
linear temporal properties without next-time on the observed atoms are preserved by stubborn
sets (`Cslib.Computability.PetriNets.Decision.AmpleLTL`) but not by the structural reduction,
which deletes places. Nothing is claimed here for those properties.

## Main definitions

- `PetriNet.StubbornDeadlockWithin`: a dead marking among the stubborn-reduced reachable
  markings within `n` steps.
- `PetriNet.reducedClosedLevel`: a closed level of the stubborn-reduced reachable markings of a
  bounded net, found by search.
- `PetriNet.decidableDeadlockOfReducesToStubborn`,
  `PetriNet.decidableDeadlockFreeOfReducesToStubborn`: deadlock reachability and
  deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, from a certificate
  `ReducesTo N M₀ N' M₀'` and a closed level of the reduced graph (`…AtLevel`), or from the
  boundedness of `N'`.
- `PetriNet.decideDeadlockStubborn`, `PetriNet.decideDeadlockFreeStubborn`: the same for the
  net found by the automatic search `PetriNet.reduce`.

## Main statements

- `PetriNet.exists_dead_iff_stubbornDeadlockWithin`: at a closed level of the stubborn-reduced
  graph of any net, a dead marking is reachable iff the level contains one.
- `PetriNet.exists_reducedClosed`: a bounded net has a closed level of the reduced graph, for
  any selector.
- `PetriNet.ReducesTo.exists_dead_iff_stubbornDeadlockWithin`: the composition.

Unlike the decision procedures of `Cslib.Computability.PetriNets.Decision.Reduced`, the
procedures with an explicit level (`…AtLevel`) do not need the reduced net to be bounded in order
to be defined, and do not explore the full reachable markings of `N'`: the closed level is checked
by `decide +kernel` on the reduced graph alone.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open scoped PetriNet

section Closed

variable {Place Transition : Type*} [DecidableEq Place] {N : PetriNet Place Transition}
  (sel : Marking Place → Finset Transition) {M₀ : Marking Place}

/-- The levels of `reducedReachSet` increase. -/
theorem reducedReachSet_mono {n k : ℕ} (h : n ≤ k) :
    N.reducedReachSet sel M₀ n ⊆ N.reducedReachSet sel M₀ k := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- A marking reached in the reduced graph from a marking of level `n` is in the level
`n + ρ.length`. -/
theorem mem_reducedReachSet_of_mTr {M M' : Marking Place} {ρ : List Transition}
    (h : (N.reduced (sel ·)).MTr M ρ M') {n : ℕ} (hM : M ∈ N.reducedReachSet sel M₀ n) :
    M' ∈ N.reducedReachSet sel M₀ (n + ρ.length) := by
  induction h generalizing n with
  | refl => exact hM
  | @stepL M₁ μ M₂ ρ M₃ htr _ ih =>
    obtain ⟨hμ, hf⟩ := htr
    have hM₂ : M₂ ∈ N.reducedReachSet sel M₀ (n + 1) := by
      refine Finset.mem_union_right _ ?_
      simp only [reducedStepSet, Finset.mem_biUnion, Option.mem_toFinset]
      exact ⟨M₁, hM, μ, hμ, fire?_eq_some_iff.2 hf⟩
    have e : n + (μ :: ρ).length = n + 1 + ρ.length := by
      rw [List.length_cons]
      omega
    exact e ▸ ih hM₂

/-- A bounded net has a closed level of the markings reachable in the graph reduced by any
selector. -/
theorem exists_reducedClosed [Finite Place] (hb : N.Bounded M₀) :
    ∃ n, N.ReducedClosed sel M₀ n := by
  have hT : {M | (N.reduced (sel ·)).CanReach M₀ M}.Finite :=
    hb.finite_reachable.subset fun _ ⟨ρ, hρ⟩ => ⟨ρ, hρ.of_reduced⟩
  have hex : ∀ M ∈ {M | (N.reduced (sel ·)).CanReach M₀ M},
      ∃ n, M ∈ N.reducedReachSet sel M₀ n := by
    rintro M ⟨ρ, hρ⟩
    exact ⟨0 + ρ.length, mem_reducedReachSet_of_mTr sel hρ (mem_reducedReachSet_self 0)⟩
  choose! g hg using hex
  obtain ⟨K, hK⟩ := Set.Finite.bddAbove (hT.image g)
  refine ⟨K, fun x hx => ?_⟩
  have hx' : x ∈ N.reducedReachSet sel M₀ (K + 1) := Finset.mem_union_right _ hx
  have hxr := reducedReachSet_reachable hx'
  exact reducedReachSet_mono sel (hK ⟨x, hxr, rfl⟩) (hg x hxr)

end Closed

section Stubborn

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : PetriNet Place Transition)

/-- A dead marking lies among the markings reachable from `M₀` within `n` steps of the graph
reduced by the computed stubborn sets. -/
def StubbornDeadlockWithin (M₀ : Marking Place) (n : ℕ) : Prop :=
  ∃ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∀ t, ¬ M [t⟩[N]

instance (M₀ : Marking Place) (n : ℕ) : Decidable (N.StubbornDeadlockWithin M₀ n) :=
  inferInstanceAs (Decidable (∃ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∀ t, ¬ M [t⟩[N]))

variable {N}

/-- At a closed level of the graph reduced by the computed stubborn sets, a dead marking is
reachable in the net iff the level contains one. -/
theorem exists_dead_iff_stubbornDeadlockWithin {M₀ : Marking Place} {n : ℕ}
    (hc : N.ReducedClosed N.stubbornFinset M₀ n) :
    (∃ M, M₀ ⇝[N] M ∧ N.Dead M) ↔ N.StubbornDeadlockWithin M₀ n := by
  constructor
  · rintro ⟨D, hr, hd⟩
    obtain ⟨D', hd', ρ, hρ⟩ := (canReach_dead_iff_reduced_stubbornFinset M₀).1 ⟨D, hd, hr⟩
    exact ⟨D', mem_of_reduced_mTr hc hρ (mem_reducedReachSet_self n), dead_iff.1 hd'⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨M, reducedReachSet_subset hM, dead_iff.2 hd⟩

/-- At a closed level of the graph reduced by the computed stubborn sets, no reachable marking is
dead iff every marking in the level enables a transition. -/
theorem deadlockFree_iff_forall_reducedReachSet {M₀ : Marking Place} {n : ℕ}
    (hc : N.ReducedClosed N.stubbornFinset M₀ n) :
    (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) ↔
      ∀ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∃ t, M [t⟩[N] := by
  have h := not_congr (exists_dead_iff_stubbornDeadlockWithin hc)
  simp only [not_exists, not_and, StubbornDeadlockWithin, not_forall, not_not] at h
  exact h

/-- A closed level of the stubborn-reduced reachable markings of a bounded net, found by
search. -/
def reducedClosedLevel [Finite Place] (M₀ : Marking Place) (hb : N.Bounded M₀) : ℕ :=
  searchNat (N.ReducedClosed N.stubbornFinset M₀) (exists_reducedClosed _ hb)

theorem reducedClosed_reducedClosedLevel [Finite Place] {M₀ : Marking Place}
    (hb : N.Bounded M₀) : N.ReducedClosed N.stubbornFinset M₀ (reducedClosedLevel M₀ hb) :=
  searchNat_spec (N.ReducedClosed N.stubbornFinset M₀) (exists_reducedClosed _ hb)

/-- Reachability of a dead marking is decidable for bounded nets, by exploring only the graph
reduced by the computed stubborn sets. -/
def decidableDeadlockStubborn [Finite Place] (M₀ : Marking Place) (hb : N.Bounded M₀) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidable_of_iff (N.StubbornDeadlockWithin M₀ (reducedClosedLevel M₀ hb))
    (exists_dead_iff_stubbornDeadlockWithin (reducedClosed_reducedClosedLevel hb)).symm

end Stubborn

section ReducesTo

universe u v

variable {Place Place' : Type u} {Transition Transition' : Type v}
  [LinearOrder Place'] [LinearOrder Transition'] [Fintype Transition']
  {N : PetriNet Place Transition} {M₀ : Marking Place}
  {N' : PetriNet Place' Transition'} {M₀' : Marking Place'}

/-- A dead marking is reachable in `N` iff the graph of the reduced net `N'` reduced by the
computed stubborn sets reaches one: the composition of the structural reduction and the
partial-order reduction. The level is closed for the stubborn-reduced graph of `N'`. -/
theorem ReducesTo.exists_dead_iff_stubbornDeadlockWithin (h : ReducesTo N M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    (∃ M, M₀ ⇝[N] M ∧ N.Dead M) ↔ N'.StubbornDeadlockWithin M₀' n :=
  h.exists_dead_iff.symm.trans (PetriNet.exists_dead_iff_stubbornDeadlockWithin hc)

/-- A dead marking is reachable in `N` iff the graph of the reduced net `N'` reduced by the
computed stubborn sets reaches one, in the formulation of
`canReach_dead_iff_reduced_stubbornFinset`. -/
theorem ReducesTo.exists_dead_iff_reduced (h : ReducesTo N M₀ N' M₀') :
    (∃ M, M₀ ⇝[N] M ∧ N.Dead M) ↔
      ∃ D, N'.Dead D ∧ (N'.reduced (N'.stubbornFinset ·)).CanReach M₀' D :=
  h.exists_dead_iff.symm.trans
    ((exists_congr fun _ => and_comm).trans (canReach_dead_iff_reduced_stubbornFinset _))

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of `N'`, from a
closed level of that graph. -/
def decidableDeadlockOfReducesToStubbornAtLevel (h : ReducesTo N M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidable_of_iff (N'.StubbornDeadlockWithin M₀' n)
    (h.exists_dead_iff_stubbornDeadlockWithin hc).symm

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, from a closed level of
that graph. -/
def decidableDeadlockFreeOfReducesToStubbornAtLevel (h : ReducesTo N M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    Decidable (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) :=
  have := decidableDeadlockOfReducesToStubbornAtLevel h hc
  decidable_of_iff (¬ ∃ M, M₀ ⇝[N] M ∧ N.Dead M) (by simp only [not_exists, not_and])

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of `N'`, which
has to be bounded. -/
def decidableDeadlockOfReducesToStubborn [Finite Place'] (h : ReducesTo N M₀ N' M₀')
    (hb : N'.Bounded M₀') : Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidableDeadlockOfReducesToStubbornAtLevel h (reducedClosed_reducedClosedLevel hb)

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, which has to be
bounded. -/
def decidableDeadlockFreeOfReducesToStubborn [Finite Place'] (h : ReducesTo N M₀ N' M₀')
    (hb : N'.Bounded M₀') : Decidable (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) :=
  decidableDeadlockFreeOfReducesToStubbornAtLevel h (reducedClosed_reducedClosedLevel hb)

end ReducesTo

section Auto

variable {n m : ℕ} (N : PetriNet (Fin n) (Fin m)) (M₀ : Marking (Fin n))

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of the
automatically reduced net, from a closed level `k` of that graph. -/
def decideDeadlockStubborn {k : ℕ}
    (hc : (reduce N M₀).net.ReducedClosed (reduce N M₀).net.stubbornFinset (reduce N M₀).init k) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidableDeadlockOfReducesToStubbornAtLevel (reduce N M₀).reduces hc

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of the automatically reduced
net, from a closed level `k` of that graph. -/
def decideDeadlockFreeStubborn {k : ℕ}
    (hc : (reduce N M₀).net.ReducedClosed (reduce N M₀).net.stubbornFinset (reduce N M₀).init k) :
    Decidable (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) :=
  decidableDeadlockFreeOfReducesToStubbornAtLevel (reduce N M₀).reduces hc

/-- Reachability of a dead marking in the bounded net `N`, decided on the stubborn-reduced graph
of the automatically reduced net. -/
def decideDeadlockReducedStubborn (hb : N.Bounded M₀) :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  decidableDeadlockOfReducesToStubborn (reduce N M₀).reduces
    ((reduce N M₀).reduces.bounded_iff.2 hb)

/-- Deadlock-freedom of the bounded net `N`, decided on the stubborn-reduced graph of the
automatically reduced net. -/
def decideDeadlockFreeReducedStubborn (hb : N.Bounded M₀) :
    Decidable (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) :=
  decidableDeadlockFreeOfReducesToStubborn (reduce N M₀).reduces
    ((reduce N M₀).reduces.bounded_iff.2 hb)

end Auto

end PetriNet

end Cslib
