/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableAutoDecisions
public import Cslib.Computability.PetriNets.ExecutableStubborn

/-! # Deadlocks through a reduction and stubborn sets

Two reductions of the state space of a net can be composed.

* A *structural reduction* (`ExecPetriNet.ReducesTo`) replaces the net `N` by a smaller net `N'`:
  fewer places and transitions, and, for series fusions, fewer reachable markings. It preserves
  the reachability of a dead marking (`ExecPetriNet.ReducesTo.exists_dead_iff`).
* A *partial-order reduction* by stubborn sets (`ExecPetriNet.stubbornFinset`) explores only the
  firings of a computed stubborn set at each marking. It preserves the reachability of a dead
  marking (`ExecPetriNet.canReach_dead_iff_reduced`), without any assumption on the net.

Applied one after the other, a dead marking is reachable in `N` if and only if the stubborn-reduced
graph of `N'` reaches a dead marking. This is decided by computing the reduced reachable markings
of `N'`, `ExecPetriNet.reducedReachSet`, up to a *closed* level, `ExecPetriNet.ReducedClosed`:
the structural reduction removes the sequences of series transitions, and the stubborn sets
remove the interleavings of the independent parts that remain.

Only deadlocks are preserved by both. Liveness and boundedness are preserved by the structural
reduction but not by stubborn sets, which may omit the firings that are needed for them, and
linear temporal properties without next-time on the observed atoms are preserved by stubborn
sets (`Cslib.Computability.PetriNets.ExecutableAmpleLTL`) but not by the structural reduction,
which deletes places. Nothing is claimed here for those properties.

## Main definitions

- `ExecPetriNet.StubbornDeadlockWithin`: a dead marking among the stubborn-reduced reachable
  markings within `n` steps.
- `ExecPetriNet.reducedClosedLevel`: a closed level of the reduced reachable markings of a bounded
  net, found by search.
- `ExecPetriNet.decidableDeadlockOfReducesToStubborn`,
  `ExecPetriNet.decidableDeadlockFreeOfReducesToStubborn`: deadlock reachability and
  deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, from a certificate
  `N.ReducesTo M₀ N' M₀'` and a closed level of the reduced graph (`…AtLevel`), or from the
  boundedness of `N'`.
- `ExecPetriNet.decideDeadlockStubborn`, `ExecPetriNet.decideDeadlockFreeStubborn`: the same for the
  net found by the automatic search `ExecPetriNet.reduce`.

## Main statements

- `ExecPetriNet.exists_dead_iff_stubbornDeadlockWithin`: at a closed level of the reduced graph of
  any executable net, a dead marking is reachable iff the level contains one.
- `ExecPetriNet.exists_reducedClosed`: a bounded net has a closed level of the reduced graph, for
  any selector.
- `ExecPetriNet.ReducesTo.exists_dead_iff_stubbornDeadlockWithin`: the composition.

Unlike the decision procedures of `Cslib.Computability.PetriNets.ExecutableReducedDecisions`, the
procedures with an explicit level (`…AtLevel`) do not need the reduced net to be bounded in order
to be defined, and do not explore the full reachable markings of `N'`: the closed level is checked
by `decide +kernel` on the reduced graph alone.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

section Closed

variable {Place Transition : Type*} [LinearOrder Place] {N : ExecPetriNet Place Transition}
  (sel : Multiset Place → Finset Transition) {M₀ : Multiset Place}

/-- The levels of `reducedReachSet` increase. -/
theorem reducedReachSet_mono {n k : ℕ} (h : n ≤ k) :
    N.reducedReachSet sel M₀ n ⊆ N.reducedReachSet sel M₀ k := by
  induction h with
  | refl => exact subset_rfl
  | step _ ih => exact ih.trans Finset.subset_union_left

/-- A marking reached in the reduced graph from a marking of level `n` is in the level
`n + ρ.length`. -/
theorem mem_reducedReachSet_of_mTr {M M' : Marking Place} {ρ : List Transition}
    (h : (N.toPetriNet.reduced (finsetSelector sel)).MTr M ρ M') :
    ∀ (m : Multiset Place) (n : ℕ), M = Multiset.toFinsupp m →
      m ∈ N.reducedReachSet sel M₀ n →
      ∃ m', M' = Multiset.toFinsupp m' ∧ m' ∈ N.reducedReachSet sel M₀ (n + ρ.length) := by
  induction h with
  | refl => exact fun m n h hm => ⟨m, h, hm⟩
  | @stepL M₁ μ M₂ ρ M₃ htr _ ih =>
    intro m n rfl hm
    obtain ⟨hμ, hf⟩ := htr
    obtain ⟨m₂, rfl, hf₂⟩ := (fires_toFinsupp_iff N).1 hf
    rw [finsetSelector_toFinsupp] at hμ
    have hm₂ : m₂ ∈ N.reducedReachSet sel M₀ (n + 1) := by
      refine Finset.mem_union_right _ ?_
      simp only [reducedStepSet, Finset.mem_biUnion, Option.mem_toFinset]
      exact ⟨m, hm, μ, by simpa using hμ, hf₂⟩
    obtain ⟨m', h', hm'⟩ := ih m₂ (n + 1) rfl hm₂
    have e : n + (μ :: ρ).length = n + 1 + ρ.length := by
      simp only [List.length_cons]
      omega
    exact ⟨m', h', e ▸ hm'⟩

/-- A bounded net has a closed level of the markings reachable in the graph reduced by any
selector. -/
theorem exists_reducedClosed [Finite Place] (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    ∃ n, N.ReducedClosed sel M₀ n := by
  have hT := hb.finite_reachable.preimage
    (f := (Multiset.toFinsupp : Multiset Place → Marking Place))
    Multiset.toFinsupp.injective.injOn
  have hT' : {m : Multiset Place | (N.toPetriNet.reduced (finsetSelector sel)).CanReach
      (Multiset.toFinsupp M₀) (Multiset.toFinsupp m)}.Finite :=
    hT.subset fun m ⟨ρ, hρ⟩ => ⟨ρ, hρ.of_reduced⟩
  have hex : ∀ m ∈ {m : Multiset Place | (N.toPetriNet.reduced (finsetSelector sel)).CanReach
      (Multiset.toFinsupp M₀) (Multiset.toFinsupp m)}, ∃ n, m ∈ N.reducedReachSet sel M₀ n := by
    rintro m ⟨ρ, hρ⟩
    obtain ⟨m', h, hm'⟩ := mem_reducedReachSet_of_mTr sel hρ M₀ 0 rfl (mem_reducedReachSet_self 0)
    exact ⟨0 + ρ.length, by rwa [Multiset.toFinsupp.injective h]⟩
  choose! g hg using hex
  obtain ⟨K, hK⟩ := Set.Finite.bddAbove (hT'.image g)
  refine ⟨K, fun x hx => ?_⟩
  have hx' : x ∈ N.reducedReachSet sel M₀ (K + 1) := Finset.mem_union_right _ hx
  have hxr := reducedReachSet_reachable hx'
  exact reducedReachSet_mono sel (hK ⟨x, hxr, rfl⟩) (hg x hxr)

end Closed

section Stubborn

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : ExecPetriNet Place Transition)

/-- A dead marking lies among the markings reachable from `M₀` within `n` steps of the graph
reduced by the computed stubborn sets. -/
def StubbornDeadlockWithin (M₀ : Multiset Place) (n : ℕ) : Prop :=
  ∃ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∀ t, ¬ N.pre t ≤ M

instance (M₀ : Multiset Place) (n : ℕ) : Decidable (N.StubbornDeadlockWithin M₀ n) :=
  inferInstanceAs (Decidable (∃ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∀ t, ¬ N.pre t ≤ M))

variable {N}

/-- At a closed level of the graph reduced by the computed stubborn sets, a dead marking is
reachable in the net iff the level contains one. -/
theorem exists_dead_iff_stubbornDeadlockWithin {M₀ : Multiset Place} {n : ℕ}
    (hc : N.ReducedClosed N.stubbornFinset M₀ n) :
    (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) ↔
      N.StubbornDeadlockWithin M₀ n := by
  constructor
  · rintro ⟨D, hr, hd⟩
    obtain ⟨D', hd', ⟨ρ, hρ⟩⟩ := (canReach_dead_iff_reduced (N := N) (Multiset.toFinsupp M₀)).1
      ⟨D, hd, hr⟩
    obtain ⟨m, hm, rfl⟩ := mem_of_reduced_mTr hc hρ M₀ (mem_reducedReachSet_self n) rfl
    exact ⟨m, hm, dead_toFinsupp_iff.1 hd'⟩
  · rintro ⟨m, hm, hd⟩
    obtain ⟨D, hd', hr⟩ := (canReach_dead_iff_reduced (N := N) (Multiset.toFinsupp M₀)).2
      ⟨Multiset.toFinsupp m, dead_toFinsupp_iff.2 hd, reducedReachSet_reachable hm⟩
    exact ⟨D, hr, hd'⟩

/-- At a closed level of the graph reduced by the computed stubborn sets, no reachable marking is
dead iff every marking in the level enables a transition. -/
theorem deadlockFree_iff_forall_reducedReachSet {M₀ : Multiset Place} {n : ℕ}
    (hc : N.ReducedClosed N.stubbornFinset M₀ n) :
    (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) ↔
      ∀ M ∈ N.reducedReachSet N.stubbornFinset M₀ n, ∃ t, N.pre t ≤ M := by
  have h := not_congr (exists_dead_iff_stubbornDeadlockWithin hc)
  simp only [not_exists, not_and, StubbornDeadlockWithin, not_forall, not_not] at h
  exact h

/-- A closed level of the reduced reachable markings of a bounded net, found by search. -/
def reducedClosedLevel [Finite Place] (M₀ : Multiset Place)
    (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) : ℕ :=
  searchNat (N.ReducedClosed N.stubbornFinset M₀) (exists_reducedClosed _ hb)

theorem reducedClosed_reducedClosedLevel [Finite Place] {M₀ : Multiset Place}
    (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    N.ReducedClosed N.stubbornFinset M₀ (reducedClosedLevel M₀ hb) :=
  searchNat_spec (N.ReducedClosed N.stubbornFinset M₀) (exists_reducedClosed _ hb)

/-- Reachability of a dead marking is decidable for bounded executable nets, by exploring only
the graph reduced by the computed stubborn sets. -/
def decidableDeadlockStubborn [Finite Place] (M₀ : Multiset Place)
    (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  decidable_of_iff (N.StubbornDeadlockWithin M₀ (reducedClosedLevel M₀ hb))
    (exists_dead_iff_stubbornDeadlockWithin (reducedClosed_reducedClosedLevel hb)).symm

end Stubborn

section ReducesTo

universe u v

variable {Place Place' : Type u} {Transition Transition' : Type v}
  [DecidableEq Place] [LinearOrder Place'] [LinearOrder Transition'] [Fintype Transition']
  {N : ExecPetriNet Place Transition} {M₀ : Multiset Place}
  {N' : ExecPetriNet Place' Transition'} {M₀' : Multiset Place'}

/-- A dead marking is reachable in `N` iff the graph of the reduced net `N'` reduced by the
computed stubborn sets reaches one: the composition of the structural reduction and the
partial-order reduction. The level is closed for the stubborn-reduced graph of `N'`. -/
theorem ReducesTo.exists_dead_iff_stubbornDeadlockWithin (h : N.ReducesTo M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) ↔
      N'.StubbornDeadlockWithin M₀' n :=
  h.exists_dead_iff.symm.trans (ExecPetriNet.exists_dead_iff_stubbornDeadlockWithin hc)

/-- A dead marking is reachable in `N` iff the graph of the reduced net `N'` reduced by the
computed stubborn sets reaches one, in the formulation of `canReach_dead_iff_reduced`. -/
theorem ReducesTo.exists_dead_iff_reduced (h : N.ReducesTo M₀ N' M₀') :
    (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) ↔
      ∃ D, N'.toPetriNet.Dead D ∧
        (N'.toPetriNet.reduced N'.stubbornSelector).CanReach (Multiset.toFinsupp M₀') D :=
  h.exists_dead_iff.symm.trans
    ((exists_congr fun _ => and_comm).trans (canReach_dead_iff_reduced _))

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of `N'`, from a
closed level of that graph. -/
def decidableDeadlockOfReducesToStubbornAtLevel (h : N.ReducesTo M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  decidable_of_iff (N'.StubbornDeadlockWithin M₀' n)
    (h.exists_dead_iff_stubbornDeadlockWithin hc).symm

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, from a closed level of
that graph. -/
def decidableDeadlockFreeOfReducesToStubbornAtLevel (h : N.ReducesTo M₀ N' M₀') {n : ℕ}
    (hc : N'.ReducedClosed N'.stubbornFinset M₀' n) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  have := decidableDeadlockOfReducesToStubbornAtLevel h hc
  decidable_of_iff (¬ ∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M)
    (by simp only [not_exists, not_and])

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of `N'`, which
has to be bounded. -/
def decidableDeadlockOfReducesToStubborn [Finite Place'] (h : N.ReducesTo M₀ N' M₀')
    (hb : N'.toPetriNet.Bounded (Multiset.toFinsupp M₀')) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  decidableDeadlockOfReducesToStubbornAtLevel h (reducedClosed_reducedClosedLevel hb)

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of `N'`, which has to be
bounded. -/
def decidableDeadlockFreeOfReducesToStubborn [Finite Place'] (h : N.ReducesTo M₀ N' M₀')
    (hb : N'.toPetriNet.Bounded (Multiset.toFinsupp M₀')) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableDeadlockFreeOfReducesToStubbornAtLevel h (reducedClosed_reducedClosedLevel hb)

end ReducesTo

section Auto

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n))

/-- Reachability of a dead marking in `N`, decided on the stubborn-reduced graph of the
automatically reduced net, from a closed level `k` of that graph. -/
def decideDeadlockStubborn {k : ℕ}
    (hc : (reduce N M₀).net.ReducedClosed (reduce N M₀).net.stubbornFinset (reduce N M₀).init k) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  decidableDeadlockOfReducesToStubbornAtLevel (reduce N M₀).reduces hc

/-- Deadlock-freedom of `N`, decided on the stubborn-reduced graph of the automatically reduced
net, from a closed level `k` of that graph. -/
def decideDeadlockFreeStubborn {k : ℕ}
    (hc : (reduce N M₀).net.ReducedClosed (reduce N M₀).net.stubbornFinset (reduce N M₀).init k) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableDeadlockFreeOfReducesToStubbornAtLevel (reduce N M₀).reduces hc

/-- Reachability of a dead marking in the bounded net `N`, decided on the stubborn-reduced graph
of the automatically reduced net. -/
def decideDeadlockReducedStubborn (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  decidableDeadlockOfReducesToStubborn (reduce N M₀).reduces
    ((reduce N M₀).reduces.bounded_iff.2 hb)

/-- Deadlock-freedom of the bounded net `N`, decided on the stubborn-reduced graph of the
automatically reduced net. -/
def decideDeadlockFreeReducedStubborn (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableDeadlockFreeOfReducesToStubborn (reduce N M₀).reduces
    ((reduce N M₀).reduces.bounded_iff.2 hb)

end Auto

end ExecPetriNet

end Cslib
