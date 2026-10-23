/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableStubborn
public import Cslib.Foundations.Semantics.LTS.AmpleSets

/-! # Partial-order reduction of executable nets for safety properties

The computed stubborn sets of `ExecPetriNet.stubbornFinset` become ample sets for the generic theory
of `LTS.IsAmple`, for a set `V` of *visible* transitions and a *level* function on markings. At a
marking the selector takes the stubborn set, except that it takes all transitions when

* a visible transition is enabled and in the stubborn set (condition `C2`), or
* some enabled transition in the stubborn set does not strictly increase the level (the cycle
  proviso `C3`).

Condition `C1` holds because the stubborn set is stubborn, and `C0` because the stubborn set
contains an enabled transition at a non-dead marking.

## Main definitions

- `ExecPetriNet.ampleFinset`: the selected transitions at a marking.
- `ExecPetriNet.ampleSelector`: the selector for `PetriNet.reduced`.
- `ExecPetriNet.LevelBounded`: the level is bounded on the reduced reachable markings.
- `ExecPetriNet.ampleReachSet`: the markings reachable in at most `n` steps of the reduced graph,
  computed, and `ExecPetriNet.AmpleClosed` says that this level is closed.

## Main statements

- `ExecPetriNet.ampleSelector_isAmple`: `C0`, `C1` and `C2`.
- `ExecPetriNet.ampleSelector_cycleProviso`: `C3`, when the level function is bounded on the
  reduced reachable markings.
- `ExecPetriNet.invariant_iff_reduced`: a predicate on markings that invisible transitions do not
  change is an invariant of the net if and only if it is an invariant of the reduced graph.
- `ExecPetriNet.forall_reachable_of_ampleReachSet`: the invariant can be checked, for example by
  `decide`, on a closed level of `ampleReachSet`; no bound on the level function is needed then.

## What is and is not covered

This is the safety fragment: reachability and invariants over finite firing sequences. The
preservation of LTL without next-time over finite and infinite maximal firing sequences is in
`Cslib.Computability.PetriNets.ExecutableAmpleLTL`.
The level function is a user-supplied sufficient condition for the cycle proviso. A level function
that makes every marking closing is always valid, but then nothing is reduced.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : ExecPetriNet Place Transition)

/-- The marking `M` is closing for `lvl`: some enabled transition of the stubborn set does not
strictly increase the level. At such markings all transitions are selected. -/
def Closing (lvl : Multiset Place → ℕ) (M : Multiset Place) : Prop :=
  ∃ t ∈ N.stubbornFinset M, N.pre t ≤ M ∧ ¬ lvl M < lvl (M - N.pre t + N.post t)

instance (lvl : Multiset Place → ℕ) (M : Multiset Place) : Decidable (N.Closing lvl M) :=
  inferInstanceAs (Decidable (∃ t ∈ _, N.pre t ≤ M ∧ _))

/-- The computed stubborn set at `M` contains an enabled visible transition. -/
def HitsVisible (V : Finset Transition) (M : Multiset Place) : Prop :=
  ∃ t ∈ N.stubbornFinset M, N.pre t ≤ M ∧ t ∈ V

instance (V : Finset Transition) (M : Multiset Place) : Decidable (N.HitsVisible V M) :=
  inferInstanceAs (Decidable (∃ t ∈ _, _))

/-- The selected transitions at `M`: all of them at closing markings and where the stubborn set
contains an enabled visible transition, and the stubborn set otherwise. -/
def ampleFinset (lvl : Multiset Place → ℕ) (V : Finset Transition) (M : Multiset Place) :
    Finset Transition :=
  if N.Closing lvl M ∨ N.HitsVisible V M then Finset.univ else N.stubbornFinset M

/-- The selector of `PetriNet.reduced` given by `ampleFinset`. -/
noncomputable abbrev ampleSelector (lvl : Multiset Place → ℕ) (V : Finset Transition) :
    Marking Place → Set Transition :=
  finsetSelector (N.ampleFinset lvl V)

variable {N} {lvl : Multiset Place → ℕ} {V : Finset Transition}

theorem ampleSelector_toFinsupp (M : Multiset Place) :
    N.ampleSelector lvl V (Multiset.toFinsupp M) = N.ampleFinset lvl V M :=
  finsetSelector_toFinsupp _ M

/-- The selected transitions are all transitions when the marking is closing or the stubborn set
contains an enabled visible transition. -/
theorem ampleFinset_of_cond {M : Multiset Place} (h : N.Closing lvl M ∨ N.HitsVisible V M) :
    N.ampleFinset lvl V M = Finset.univ := by simp [ampleFinset, h]

/-- Otherwise they are the computed stubborn set. -/
theorem ampleFinset_of_not {M : Multiset Place} (h : ¬ (N.Closing lvl M ∨ N.HitsVisible V M)) :
    N.ampleFinset lvl V M = N.stubbornFinset M := by simp [ampleFinset, h]

/-- The conditions `C0`, `C1` and `C2` for the selector `ampleSelector`: the transitions outside
`V` are invisible. -/
theorem ampleSelector_isAmple :
    N.toPetriNet.lts.IsAmple (N.ampleSelector lvl V) (· ∉ V) := by
  refine ⟨fun M hM => ?_, fun M => ?_, fun M hM μ hμ hen => ?_⟩
  · obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective M
    obtain ⟨t, M', ht⟩ : ∃ t M', N.toPetriNet.lts.Tr (Multiset.toFinsupp M) t M' := by
      by_contra hc
      push Not at hc
      exact hM fun t M' h => hc t M' h
    rw [ampleSelector_toFinsupp]
    by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · exact ⟨t, by simp [ampleFinset_of_cond hc], _, ht⟩
    · have hdead : ¬ N.toPetriNet.Dead (Multiset.toFinsupp M) := fun hd => hd t M' ht
      obtain ⟨t, htS, hen⟩ := exists_enabled_mem_stubbornFinset hdead
      exact ⟨t, by simpa [ampleFinset_of_not hc] using htS, enabled_iff_exists_fires.1 hen⟩
  · obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective M
    rw [ampleSelector_toFinsupp]
    by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · rw [ampleFinset_of_cond hc]
      simpa using LTS.isStubborn_univ (lts := N.toPetriNet.lts) (Multiset.toFinsupp M)
    · rw [ampleFinset_of_not hc]
      exact stubbornFinset_isStubborn M
  · obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective M
    rw [ampleSelector_toFinsupp] at hμ
    by_cases hc : N.Closing lvl M ∨ N.HitsVisible V M
    · exact absurd (fun ν _ => by rw [ampleSelector_toFinsupp, ampleFinset_of_cond hc]; simp) hM
    · rw [ampleFinset_of_not hc] at hμ
      obtain ⟨M', hM'⟩ := hen
      refine fun hv => hc (Or.inr ⟨μ, hμ, ?_, hv⟩)
      exact enabled_toPetriNet_iff.1 (enabled_iff_exists_fires.2 ⟨M', hM'⟩)

/-- The level is at most `B` on the markings reachable from `M₀` in the graph reduced by
`ampleSelector`. -/
def LevelBounded (N : ExecPetriNet Place Transition) (lvl : Multiset Place → ℕ)
    (V : Finset Transition) (B : ℕ) (M₀ : Marking Place) : Prop :=
  ∀ M, (N.toPetriNet.reduced (N.ampleSelector lvl V)).CanReach M₀ M →
    lvl (Multiset.toFinsupp.symm M) ≤ B

/-- The cycle proviso `C3` for the selector `ampleSelector`, if the level is bounded on the
markings reachable from `M₀` in the reduced graph. -/
theorem ampleSelector_cycleProviso {B : ℕ} {M₀ : Marking Place} (hB : N.LevelBounded lvl V B M₀) :
    N.toPetriNet.lts.CycleProviso (N.ampleSelector lvl V) M₀ := by
  refine LTS.CycleProviso.of_level (fun M => lvl (Multiset.toFinsupp.symm M)) B hB
    fun M M' _ ⟨hne, μ, hsel, hμ⟩ => ?_
  obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective M
  have hc : ¬ (N.Closing lvl M ∨ N.HitsVisible V M) := fun hc =>
    hne fun ν _ => by rw [ampleSelector_toFinsupp, ampleFinset_of_cond hc]; simp
  obtain ⟨m', rfl, hf⟩ := (fires_toFinsupp_iff N).1 hμ
  have hle : N.pre μ ≤ M := enabled_toPetriNet_iff.1 (enabled_iff_exists_fires.2 ⟨_, hμ⟩)
  have hμ' : μ ∈ N.stubbornFinset M := by
    rw [ampleSelector_toFinsupp, ampleFinset_of_not hc] at hsel
    simpa using hsel
  have hcl : ¬ ¬ lvl M < lvl (M - N.pre μ + N.post μ) := fun h => hc (Or.inl ⟨μ, hμ', hle, h⟩)
  simp only [fire, hle, ↓reduceIte, Option.some.injEq] at hf
  subst hf
  simpa using not_not.1 hcl

/-- The markings reachable from `M₀` in at most `n` steps of the graph reduced by
`ampleSelector`. -/
abbrev ampleReachSet (lvl : Multiset Place → ℕ) (V : Finset Transition) (M₀ : Multiset Place)
    (n : ℕ) : Finset (Multiset Place) :=
  N.reducedReachSet (N.ampleFinset lvl V) M₀ n

/-- The level `n` of `ampleReachSet` is closed: it contains the markings reached by one more
selected firing. -/
abbrev AmpleClosed (lvl : Multiset Place → ℕ) (V : Finset Transition) (M₀ : Multiset Place)
    (n : ℕ) : Prop :=
  N.ReducedClosed (N.ampleFinset lvl V) M₀ n

/-- Reachability of a marking satisfying `P`, for a predicate that the transitions outside `V` do
not change, is the same in the net and in the graph reduced by `ampleSelector`. The level `lvl`
must be bounded on the reduced reachable markings. -/
theorem canReach_iff_reduced {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Marking Place → Prop} (hP : ∀ M t M', M [t⟩[N] M' → t ∉ V → (P M ↔ P M')) :
    (∃ M, M₀ ⇝[N] M ∧ P M) ↔
      ∃ M, (N.toPetriNet.reduced (N.ampleSelector lvl V)).CanReach M₀ M ∧ P M :=
  LTS.canReach_iff_reduced ampleSelector_isAmple (ampleSelector_cycleProviso hB) hP

/-- A predicate that the transitions outside `V` do not change is an invariant of the net if and
only if it is an invariant of the graph reduced by `ampleSelector`. The level `lvl` must be bounded
on the reduced reachable markings. -/
theorem invariant_iff_reduced {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Marking Place → Prop} (hP : ∀ M t M', M [t⟩[N] M' → t ∉ V → (P M ↔ P M')) :
    (∀ M, M₀ ⇝[N] M → P M) ↔
      ∀ M, (N.toPetriNet.reduced (N.ampleSelector lvl V)).CanReach M₀ M → P M :=
  LTS.invariant_iff_reduced ampleSelector_isAmple (ampleSelector_cycleProviso hB) hP

/-- Checking an invariant on a closed level of `ampleReachSet`, which can be done by `decide`,
proves it for all reachable markings. The level function needs no bound: it is bounded on the
finite closed level. -/
theorem forall_reachable_of_ampleReachSet {P : Multiset Place → Prop}
    (hP : ∀ M t, N.pre t ≤ M → t ∉ V → (P M ↔ P (M - N.pre t + N.post t)))
    {M₀ : Multiset Place} {n : ℕ} (hc : N.AmpleClosed lvl V M₀ n)
    (hall : ∀ M ∈ N.ampleReachSet lvl V M₀ n, P M) :
    ∀ M : Multiset Place, M₀ ⇝[N] M → P M := by
  have hP' : ∀ M t M', M [t⟩[N] M' → t ∉ V →
      (P (Multiset.toFinsupp.symm M) ↔ P (Multiset.toFinsupp.symm M')) := by
    intro M t M' h ht
    obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective M
    obtain ⟨m', rfl⟩ := Multiset.toFinsupp.surjective M'
    have hf := fires_iff.1 h
    have hle : N.pre t ≤ m := enabled_toPetriNet_iff.1 (enabled_iff_exists_fires.2 ⟨_, h⟩)
    simp only [fire, hle, ↓reduceIte, Option.some.injEq] at hf
    subst hf
    simpa using hP m t hle ht
  have hB : N.LevelBounded lvl V ((N.ampleReachSet lvl V M₀ n).sup lvl) (Multiset.toFinsupp M₀) :=
    fun M' ⟨ρ, hρ⟩ => by
      obtain ⟨m', hm', rfl⟩ := mem_of_reduced_mTr hc hρ M₀ (mem_reducedReachSet_self n) rfl
      simpa using Finset.le_sup (f := lvl) hm'
  intro M hM
  have := (invariant_iff_reduced hB (P := fun M => P (Multiset.toFinsupp.symm M)) hP').2 ?_
    (Multiset.toFinsupp M) hM
  · simpa using this
  · intro M' ⟨ρ, hρ⟩
    obtain ⟨m', hm', rfl⟩ := mem_of_reduced_mTr hc hρ M₀ (mem_reducedReachSet_self n) rfl
    simpa using hall m' hm'

end ExecPetriNet

end Cslib
