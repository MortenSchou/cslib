/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Independence
public import Cslib.Foundations.Semantics.LTS.Reduction

/-! # Stubborn sets and deadlock-preserving reduction

Partial-order reduction explores only some of the enabled transitions at each marking. A set of
transitions `T` is *stubborn* at `M` if firing sequences that avoid `T` neither disable an enabled
member of `T`, nor enable a disabled one, and the enabled members of `T` commute with such
sequences. Exploring only a stubborn set at each marking preserves the reachable deadlocks.

## Main definitions

- `PetriNet.IsStubborn`: stubborn sets at a marking.
- `PetriNet.StubbornClosed`: a structural criterion, due to Valmari: enabled members are not in
  conflict (`PetriNet.Conflict`) with any transition outside the set, and each disabled member has
  a place that is missing tokens and that no transition outside the set can fill.
- `PetriNet.stubbornSet`: the least set closed in this sense that contains a given transition.
- `PetriNet.stubbornSelector`: a choice of stubborn set at every marking.
- `PetriNet.reduced`: the marking graph restricted to the transitions selected at each marking.

## Main statements

- `PetriNet.StubbornClosed.isStubborn`: the structural criterion implies stubbornness.
- `PetriNet.exists_reduced_mTr_of_dead`: if a dead marking is reachable by a firing sequence, then
  it is reachable by one of the same length in the reduced graph.
- `PetriNet.canReach_dead_iff_reduced`: a dead marking is reachable from `M` iff it is
  reachable from `M` in the graph reduced by `stubbornSelector`.

This file proves deadlock preservation. The reduction also preserves safety properties and LTL
without next-time, if the selector takes all transitions when a visible transition is enabled in the
stubborn set and satisfies a cycle proviso: this is the generic theory of
`Cslib.Foundations.Semantics.LTS.AmpleSets`, instantiated to computed stubborn sets in
`Cslib.Computability.PetriNets.ExecutableAmple`.

## References

* [A. Valmari, *Stubborn sets for reduced state space generation*][Valmari1991]
* [P. Godefroid, *Partial-Order Methods for the Verification of Concurrent Systems*][Godefroid1996]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- `T` is stubborn at `M`: for every firing sequence `σ` from `M` that avoids `T`, each
transition of `T` that is enabled at `M` is enabled after `σ` and commutes with `σ`, and each
transition of `T` that is disabled at `M` is disabled after `σ`. This is `LTS.IsStubborn` of the
marking graph; see there for the relation to the literature. -/
abbrev IsStubborn (N : PetriNet Place Transition) (M : Marking Place) (T : Set Transition) :
    Prop :=
  N.lts.IsStubborn M T

/-- A structural sufficient condition for being stubborn: enabled members of `T` are not in
conflict with any transition outside `T`, and each disabled member of `T` has a place that is
missing tokens and that no transition outside `T` can fill. -/
def StubbornClosed (N : PetriNet Place Transition) (M : Marking Place) (T : Set Transition) :
    Prop :=
  (∀ t ∈ T, M [t⟩[N] → ∀ u, u ∉ T → ¬ N.Conflict t u) ∧
  (∀ t ∈ T, ¬ M [t⟩[N] → ∃ p, M p < •[N] t p ∧ ∀ u, u ∉ T → N.post u p ≤ N.pre u p)

/-- A transition that is in conflict with no transition of a sequence commutes with it. -/
theorem mTr_commute {M M' : Marking Place} {σ : List Transition} {t : Transition}
    (h : N.lts.MTr M σ M') (hd : ∀ u ∈ σ, ¬ N.Conflict t u) :
    ∀ M₁, M [t⟩[N] M₁ → ∃ M₁', M' [t⟩[N] M₁' ∧ N.lts.MTr M₁ σ M₁' := by
  induction h with
  | refl => exact fun M₁ h => ⟨M₁, h, .refl⟩
  | stepL htr _ ih =>
    intro M₁ h₁
    obtain ⟨M₃, h₃, h₄⟩ := Fires.diamond' (hd _ (List.mem_cons_self ..)) h₁ htr
    obtain ⟨M₁', h₅, h₆⟩ := ih (fun u hu => hd u (List.mem_cons_of_mem _ hu)) M₃ h₄
    exact ⟨M₁', h₅, .stepL h₃ h₆⟩

/-- A firing sequence whose transitions never increase the tokens of `p` does not increase them. -/
theorem apply_le_of_mTr {M M' : Marking Place} {σ : List Transition} {p : Place}
    (h : N.lts.MTr M σ M') (hp : ∀ u ∈ σ, N.post u p ≤ N.pre u p) : M' p ≤ M p := by
  induction h with
  | refl => exact le_rfl
  | @stepL _ v _ vs _ htr _ ih =>
    refine (ih fun u hu => hp u (List.mem_cons_of_mem _ hu)).trans ?_
    obtain ⟨R, rfl, rfl⟩ := htr
    have := hp v (List.mem_cons_self ..)
    simp only [Finsupp.add_apply]
    omega

/-- A structurally closed set is stubborn. -/
theorem StubbornClosed.isStubborn {M : Marking Place} {T : Set Transition}
    (h : StubbornClosed N M T) : IsStubborn N M T := by
  intro σ M' hσ havoid t ht
  refine ⟨fun hen => ?_, fun hdis hen => ?_⟩
  · have hen' := enabled_iff_exists_fires.2 hen
    obtain ⟨M₁, h₁⟩ := hen
    obtain ⟨M₁', h₂, _⟩ := mTr_commute hσ (fun u hu => h.1 t ht hen' u (havoid u hu)) M₁ h₁
    refine ⟨⟨_, h₂⟩, fun A B hA hB => ?_⟩
    obtain ⟨C, h₂', h₃⟩ := mTr_commute hσ (fun u hu => h.1 t ht hen' u (havoid u hu)) A hA
    obtain rfl := LTS.Deterministic.deterministic (lts := N.lts) _ _ _ _ h₂' hB
    exact h₃
  · have hdis' : ¬ M [t⟩[N] := fun h' => hdis (enabled_iff_exists_fires.1 h')
    obtain ⟨p, hp, hq⟩ := h.2 t ht hdis'
    have := apply_le_of_mTr hσ fun u hu => hq u (havoid u hu)
    exact absurd (Finsupp.le_def.1 (enabled_iff_exists_fires.2 hen) p) (by omega)

/-- The marking graph restricted to the transitions selected by `S` at each marking. -/
abbrev reduced (N : PetriNet Place Transition) (S : Marking Place → Set Transition) :
    LTS (Marking Place) Transition :=
  N.lts.reduced S

/-- Deadlock preservation. If `S` selects a stubborn set at every marking, and at every
non-dead marking the selected set contains an enabled transition, then every dead marking reachable
by a firing sequence is reachable by a firing sequence of the same length in the reduced graph. -/
theorem exists_reduced_mTr_of_dead (S : Marking Place → Set Transition)
    (hS : ∀ M, IsStubborn N M (S M)) (hne : ∀ M, ¬ N.Dead M → ∃ t ∈ S M, M [t⟩[N])
    {D : Marking Place} (hD : N.Dead D) (σ : List Transition) (M : Marking Place)
    (h : N.lts.MTr M σ D) : ∃ ρ, (N.reduced S).MTr M ρ D ∧ ρ.length = σ.length :=
  LTS.exists_reduced_mTr_of_isTerminal S hS
    (fun M hM => let ⟨t, ht, hen⟩ := hne M hM; ⟨t, ht, enabled_iff_exists_fires.1 hen⟩) hD σ M h

/-- The transition `u` is brought in by `t` in the stubborn closure at `M`: if `t` is enabled, when
`u` is in conflict with `t`, and if `t` is disabled, when `u` adds tokens to a place that `t` is
short of. -/
def StubbornRel (N : PetriNet Place Transition) (M : Marking Place) (t u : Transition) : Prop :=
  (M [t⟩[N] ∧ N.Conflict t u) ∨ (¬ M [t⟩[N] ∧ ∃ p, M p < N.pre t p ∧ N.pre u p < N.post u p)

/-- The set of transitions generated from `t₀` by `StubbornRel`. -/
def stubbornSet (N : PetriNet Place Transition) (M : Marking Place) (t₀ : Transition) :
    Set Transition :=
  {u | Relation.ReflTransGen (N.StubbornRel M) t₀ u}

/-- A disabled transition has a place where the marking is short of tokens. -/
theorem exists_missing {M : Marking Place} {t : Transition} (h : ¬ M [t⟩[N]) :
    ∃ p, M p < N.pre t p := by
  by_contra hc
  push Not at hc
  exact h (Finsupp.le_def.2 hc)

/-- `stubbornSet` is closed in the sense of `StubbornClosed`. -/
theorem stubbornSet_closed (M : Marking Place) (t₀ : Transition) :
    StubbornClosed N M (N.stubbornSet M t₀) := by
  refine ⟨fun t ht hen u hu hc => hu (ht.tail (.inl ⟨hen, hc⟩)), fun t ht hdis => ?_⟩
  obtain ⟨p, hp⟩ := exists_missing hdis
  refine ⟨p, hp, fun u hu => ?_⟩
  by_contra hlt
  exact hu (ht.tail (.inr ⟨hdis, p, hp, not_le.1 hlt⟩))

open Classical in
/-- A choice of stubborn set at every marking: the set generated by an enabled transition when
there is one, and the empty set at dead markings. -/
noncomputable def stubbornSelector (N : PetriNet Place Transition) (M : Marking Place) :
    Set Transition :=
  if h : ∃ t, M [t⟩[N] then N.stubbornSet M h.choose else ∅

/-- `stubbornSelector` selects a stubborn set at every marking. -/
theorem stubbornSelector_isStubborn (N : PetriNet Place Transition) (M : Marking Place) :
    IsStubborn N M (N.stubbornSelector M) := by
  unfold stubbornSelector
  split_ifs with h
  · exact (stubbornSet_closed M _).isStubborn
  · intro _ _ _ _ t ht
    exact absurd ht (Set.notMem_empty t)

/-- At a non-dead marking, `stubbornSelector` selects an enabled transition. -/
theorem stubbornSelector_exists_enabled (N : PetriNet Place Transition) (M : Marking Place)
    (hM : ¬ N.Dead M) : ∃ t ∈ N.stubbornSelector M, M [t⟩[N] := by
  have h : ∃ t, M [t⟩[N] := by
    by_contra hc
    push Not at hc
    exact hM (dead_iff.2 hc)
  refine ⟨h.choose, ?_, h.choose_spec⟩
  unfold stubbornSelector
  rw [dite_eq_left_of_eq_true (eq_true h)]
  exact .refl

/-- A dead marking is reachable from `M` if and only if it is reachable from `M` in the graph
reduced by a selector `S` that selects a stubborn set containing an enabled transition at every
non-dead marking. -/
theorem canReach_dead_iff_reduced_of (S : Marking Place → Set Transition)
    (hS : ∀ M, IsStubborn N M (S M)) (hne : ∀ M, ¬ N.Dead M → ∃ t ∈ S M, M [t⟩[N])
    {M : Marking Place} :
    (∃ D, N.Dead D ∧ M ⇝[N] D) ↔ ∃ D, N.Dead D ∧ (N.reduced S).CanReach M D :=
  LTS.canReach_isTerminal_iff_reduced S hS fun M hM =>
    let ⟨t, ht, hen⟩ := hne M hM
    ⟨t, ht, enabled_iff_exists_fires.1 hen⟩

/-- A dead marking is reachable from `M` if and only if it is reachable from `M` in the graph
reduced by `stubbornSelector`. -/
theorem canReach_dead_iff_reduced (N : PetriNet Place Transition) (M : Marking Place) :
    (∃ D, N.Dead D ∧ M ⇝[N] D) ↔
      ∃ D, N.Dead D ∧ (N.reduced N.stubbornSelector).CanReach M D :=
  canReach_dead_iff_reduced_of _ (stubbornSelector_isStubborn N) (stubbornSelector_exists_enabled N)

end PetriNet

end Cslib
