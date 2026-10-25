/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.Stubborn
public import Cslib.Foundations.Semantics.LTS.AmpleSets

/-! # Partial-order reduction of nets for safety properties

The computed stubborn sets of `PetriNet.stubbornFinset` become ample sets for the generic theory
of `LTS.IsAmple`, for a set `V` of *visible* transitions and a *level* function on markings. At a
marking the selector takes the stubborn set, except that it takes all transitions when

* a visible transition is enabled and in the stubborn set (condition `C2`), or
* some enabled transition in the stubborn set does not strictly increase the level (the cycle
  proviso `C3`).

Condition `C1` holds because the stubborn set is stubborn, and `C0` because the stubborn set
contains an enabled transition at a non-dead marking.

## Main definitions

- `PetriNet.ampleFinset`: the selected transitions at a marking, a selector for
  `PetriNet.reduced`.
- `PetriNet.LevelBounded`: the level is bounded on the reduced reachable markings.
- `PetriNet.ampleReachSet`: the markings reachable in at most `n` steps of the reduced graph,
  computed, and `PetriNet.AmpleClosed` says that this level is closed.

## Main statements

- `PetriNet.ampleFinset_isAmple`: `C0`, `C1` and `C2`.
- `PetriNet.ampleFinset_cycleProviso`: `C3`, when the level function is bounded on the
  reduced reachable markings.
- `PetriNet.invariant_iff_reduced`: a predicate on markings that invisible transitions do not
  change is an invariant of the net if and only if it is an invariant of the reduced graph.
- `PetriNet.forall_reachable_of_ampleReachSet`: the invariant can be checked, for example by
  `decide`, on a closed level of `ampleReachSet`; no bound on the level function is needed then.

## What is and is not covered

This is the safety fragment: reachability and invariants over finite firing sequences. The
preservation of LTL without next-time over finite and infinite maximal firing sequences is in
`Cslib.Computability.PetriNets.Decision.AmpleLTL`.
The level function is a user-supplied sufficient condition for the cycle proviso. A level function
that makes every marking closing is always valid, but then nothing is reduced.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : PetriNet Place Transition)

/-- The marking `M` is closing for `lvl`: some enabled transition of the stubborn set does not
strictly increase the level. At such markings all transitions are selected. -/
def Closing (lvl : Marking Place → ℕ) (M : Marking Place) : Prop :=
  ∃ t ∈ N.stubbornFinset M, M [t⟩[N] ∧ ¬ lvl M < lvl (N.fire M t)

instance (lvl : Marking Place → ℕ) (M : Marking Place) : Decidable (N.Closing lvl M) :=
  inferInstanceAs (Decidable (∃ t ∈ _, _ ∧ _))

/-- The computed stubborn set at `M` contains an enabled visible transition. -/
def HitsVisible (V : Finset Transition) (M : Marking Place) : Prop :=
  ∃ t ∈ N.stubbornFinset M, M [t⟩[N] ∧ t ∈ V

instance (V : Finset Transition) (M : Marking Place) : Decidable (N.HitsVisible V M) :=
  inferInstanceAs (Decidable (∃ t ∈ _, _))

/-- The selected transitions at `M`: all of them at closing markings and where the stubborn set
contains an enabled visible transition, and the stubborn set otherwise. -/
def ampleFinset (lvl : Marking Place → ℕ) (V : Finset Transition) (M : Marking Place) :
    Finset Transition :=
  if N.Closing lvl M ∨ N.HitsVisible V M then Finset.univ else N.stubbornFinset M

variable {N} {lvl : Marking Place → ℕ} {V : Finset Transition}

/-- The selected transitions are all transitions when the marking is closing or the stubborn set
contains an enabled visible transition. -/
theorem ampleFinset_of_cond {M : Marking Place} (h : N.Closing lvl M ∨ N.HitsVisible V M) :
    N.ampleFinset lvl V M = Finset.univ := by simp [ampleFinset, h]

/-- Otherwise they are the computed stubborn set. -/
theorem ampleFinset_of_not {M : Marking Place} (h : ¬ (N.Closing lvl M ∨ N.HitsVisible V M)) :
    N.ampleFinset lvl V M = N.stubbornFinset M := by simp [ampleFinset, h]

/-- The conditions `C0`, `C1` and `C2` for the selector `ampleFinset`: the transitions outside
`V` are invisible. -/
theorem ampleFinset_isAmple : N.lts.IsAmple (N.ampleFinset lvl V ·) (· ∉ V) := by
  refine ⟨fun M hM => ?_, fun M => ?_, fun M hM μ hμ hen => ?_⟩
  · by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · obtain ⟨t, M', ht⟩ : ∃ t M', N.lts.Tr M t M' := by
        by_contra hc
        push Not at hc
        exact hM fun t M' h => hc t M' h
      exact ⟨t, by simp [ampleFinset_of_cond hc], _, ht⟩
    · obtain ⟨t, htS, hen⟩ := exists_enabled_mem_stubbornFinset hM
      exact ⟨t, by simpa [ampleFinset_of_not hc] using htS, enabled_iff_exists_fires.1 hen⟩
  · by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · simpa [ampleFinset_of_cond hc] using LTS.isStubborn_univ (lts := N.lts) M
    · simpa [ampleFinset_of_not hc] using stubbornFinset_isStubborn M
  · by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · exact absurd (fun ν _ => by simp [ampleFinset_of_cond hc]) hM
    · rw [Finset.mem_coe, ampleFinset_of_not hc] at hμ
      exact fun hv => hc (Or.inr ⟨μ, hμ, enabled_iff_exists_fires.2 hen, hv⟩)

/-- The level is at most `B` on the markings reachable from `M₀` in the graph reduced by
`ampleFinset`. -/
def LevelBounded (N : PetriNet Place Transition) (lvl : Marking Place → ℕ)
    (V : Finset Transition) (B : ℕ) (M₀ : Marking Place) : Prop :=
  ∀ M, (N.reduced (N.ampleFinset lvl V ·)).CanReach M₀ M → lvl M ≤ B

/-- The cycle proviso `C3` for the selector `ampleFinset`, if the level is bounded on the
markings reachable from `M₀` in the reduced graph. -/
theorem ampleFinset_cycleProviso {B : ℕ} {M₀ : Marking Place} (hB : N.LevelBounded lvl V B M₀) :
    N.lts.CycleProviso (N.ampleFinset lvl V ·) M₀ := by
  refine LTS.CycleProviso.of_level lvl B hB fun M M' _ ⟨hne, μ, hsel, hμ⟩ => ?_
  have hc : ¬ (N.Closing lvl M ∨ N.HitsVisible V M) := fun hc =>
    hne fun ν _ => by simp [ampleFinset_of_cond hc]
  rw [Finset.mem_coe, ampleFinset_of_not hc] at hsel
  obtain ⟨hen, rfl⟩ := fires_iff.1 hμ
  by_contra hcl
  exact hc (Or.inl ⟨μ, hsel, hen, hcl⟩)

/-- The markings reachable from `M₀` in at most `n` steps of the graph reduced by
`ampleFinset`. -/
abbrev ampleReachSet (lvl : Marking Place → ℕ) (V : Finset Transition) (M₀ : Marking Place)
    (n : ℕ) : Finset (Marking Place) :=
  N.reducedReachSet (N.ampleFinset lvl V) M₀ n

/-- The level `n` of `ampleReachSet` is closed: it contains the markings reached by one more
selected firing. -/
abbrev AmpleClosed (lvl : Marking Place → ℕ) (V : Finset Transition) (M₀ : Marking Place)
    (n : ℕ) : Prop :=
  N.ReducedClosed (N.ampleFinset lvl V) M₀ n

/-- Reachability of a marking satisfying `P`, for a predicate that the transitions outside `V` do
not change, is the same in the net and in the graph reduced by `ampleFinset`. The level `lvl`
must be bounded on the reduced reachable markings. -/
theorem canReach_iff_reduced {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Marking Place → Prop} (hP : ∀ M t M', M [t⟩[N] M' → t ∉ V → (P M ↔ P M')) :
    (∃ M, M₀ ⇝[N] M ∧ P M) ↔ ∃ M, (N.reduced (N.ampleFinset lvl V ·)).CanReach M₀ M ∧ P M :=
  LTS.canReach_iff_reduced ampleFinset_isAmple (ampleFinset_cycleProviso hB) hP

/-- A predicate that the transitions outside `V` do not change is an invariant of the net if and
only if it is an invariant of the graph reduced by `ampleFinset`. The level `lvl` must be bounded
on the reduced reachable markings. -/
theorem invariant_iff_reduced {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Marking Place → Prop} (hP : ∀ M t M', M [t⟩[N] M' → t ∉ V → (P M ↔ P M')) :
    (∀ M, M₀ ⇝[N] M → P M) ↔ ∀ M, (N.reduced (N.ampleFinset lvl V ·)).CanReach M₀ M → P M :=
  LTS.invariant_iff_reduced ampleFinset_isAmple (ampleFinset_cycleProviso hB) hP

/-- Checking an invariant on a closed level of `ampleReachSet`, which can be done by `decide`,
proves it for all reachable markings. The level function needs no bound: it is bounded on the
finite closed level. -/
theorem forall_reachable_of_ampleReachSet {P : Marking Place → Prop}
    (hP : ∀ M t M', M [t⟩[N] M' → t ∉ V → (P M ↔ P M')) {M₀ : Marking Place} {n : ℕ}
    (hc : N.AmpleClosed lvl V M₀ n) (hall : ∀ M ∈ N.ampleReachSet lvl V M₀ n, P M) :
    ∀ M, M₀ ⇝[N] M → P M := by
  have hmem : ∀ M, (N.reduced (N.ampleFinset lvl V ·)).CanReach M₀ M →
      M ∈ N.ampleReachSet lvl V M₀ n :=
    fun _ ⟨_, hρ⟩ => mem_of_reduced_mTr hc hρ (mem_reducedReachSet_self n)
  have hB : N.LevelBounded lvl V ((N.ampleReachSet lvl V M₀ n).sup lvl) M₀ :=
    fun M hM => Finset.le_sup (f := lvl) (hmem M hM)
  exact (invariant_iff_reduced hB hP).2 fun M hM => hall M (hmem M hM)

end PetriNet

end Cslib
