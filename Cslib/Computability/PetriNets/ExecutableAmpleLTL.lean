/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableAmple
public import Cslib.Computability.PetriNets.LTL
public import Cslib.Logics.Temporal.LTL.AmpleSets

/-! # Partial-order reduction of executable nets preserves LTL without next-time

The ample selector `ExecPetriNet.ampleSelector` of `Cslib.Computability.PetriNets.ExecutableAmple`
satisfies `C0`, `C1` and `C2` for a set `V` of visible transitions, and `C3` for a level function
that is bounded on the reduced reachable markings. By the generic theorem
`Cslib.Logics.Temporal.LTL.AmpleSets`, the LTL formulas without next-time that observe only atoms
that the transitions outside `V` do not change hold on all maximal firing sequences of the net iff
they hold on those of the reduced marking graph, and similarly for some maximal firing sequence.

## Main definitions

- `ExecPetriNet.ampleModel`: the marking graph restricted to the selected transitions, as a model.
- `ExecPetriNet.visibleOf`: the transitions with a net effect on some place of a set of places.

## Main statements

- `ExecPetriNet.allPaths_ampleModel_iff`, `ExecPetriNet.somePath_ampleModel_iff`: preservation of
  LTL without next-time.
- `ExecPetriNet.enabled_atoms_invisible`: the atoms `enabled t` for `t` in a set `E` are not
  changed by the transitions outside `visibleOf` the places of the presets of `E`, which discharges
  the hypothesis `hS` for formulas about the enabledness of transitions.
- `ExecPetriNet.apply_eq_of_not_mem_visibleOf`: the tokens of a place of `P` are not changed by a
  transition outside `visibleOf P`, which discharges the invariance hypothesis of
  `ExecPetriNet.invariant_iff_reduced` for properties such as `k ≤ M p`.

## What is covered

The nets need not be bounded, but the level function must be, as a sufficient condition for the
cycle proviso. Both infinite and finite maximal firing sequences are covered. The user has to show
that the transitions outside `V` do not change the observed atoms (`hS`). The atom
`marking M` is only unchanged by the transitions with no net effect at all, so formulas that use it
need `V` to contain nearly all transitions, and little is reduced. The atom `enabled t` is changed
only by transitions with a net effect on the preset of `t`.
-/

@[expose] public section

namespace Cslib

open Cslib.Logic Cslib.Logic.LTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : ExecPetriNet Place Transition)

/-- The marking graph restricted to the transitions selected by `ampleSelector`, as a model with
the atoms of the net. -/
def ampleModel (lvl : Multiset Place → ℕ) (V : Finset Transition) :
    CTL.Model (Marking Place) (Atom Place Transition) :=
  ⟨N.toPetriNet.lts.reduced (N.ampleSelector lvl V), N.toPetriNet.model.v⟩

/-- The transitions with a net effect on some place of `P`: they do not leave the number of tokens
of every place of `P` unchanged. -/
def visibleOf (P : Finset Place) : Finset Transition :=
  Finset.univ.filter fun u => ∃ p ∈ P, (N.pre u).count p ≠ (N.post u).count p

variable {N} {lvl : Multiset Place → ℕ} {V : Finset Transition}

omit [LinearOrder Transition] in
/-- A transition outside `visibleOf P` does not change the tokens of the places of `P`. -/
theorem apply_eq_of_not_mem_visibleOf {P : Finset Place} {M M' : Marking Place} {t : Transition}
    (h : M [t⟩[N] M') (ht : t ∉ N.visibleOf P) {p : Place} (hp : p ∈ P) : M p = M' p :=
  h.apply_eq (by
    by_contra hne
    exact ht (Finset.mem_filter.2 ⟨Finset.mem_univ _, p, hp, hne⟩))

omit [LinearOrder Transition] in
/-- The atoms `enabled u`, for `u` in `E`, are not changed by the transitions outside `V`, if `V`
contains the transitions with a net effect on a place in the preset of a transition of `E`. -/
theorem enabled_atoms_invisible {E : Finset Transition}
    (hV : N.visibleOf (E.biUnion fun u => (N.pre u).toFinset) ⊆ V) :
    ∀ M t M' a, a ∈ {a | ∃ u ∈ E, a = Atom.enabled u} → M [t⟩[N] M' → t ∉ V →
      (N.model.v M a ↔ N.model.v M' a) := by
  rintro M t M' a ⟨u, hu, rfl⟩ h ht
  refine h.enabled_iff_of_noEffect fun p hp => ?_
  by_contra hne
  exact ht (hV (Finset.mem_filter.2 ⟨Finset.mem_univ _, p, Finset.mem_biUnion.2
    ⟨u, hu, Multiset.mem_toFinset.2 (Multiset.count_pos.1 hp)⟩, hne⟩))

/-- **Partial-order reduction of executable nets preserves LTL without next-time on all paths.**
A formula without next-time whose atoms are in `S` holds on all maximal firing sequences from a
marking iff it holds on all those of the reduced marking graph, if the transitions outside `V`
do not change the atoms in `S`, and the level function is bounded on the reduced reachable
markings. -/
theorem allPaths_ampleModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {S : Set (Atom Place Transition)}
    (hS : ∀ M t M' a, a ∈ S → M [t⟩[N] M' → t ∉ V → (N.model.v M a ↔ N.model.v M' a))
    {φ : Formula (Atom Place Transition)} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[N.model,M₀ ⊨∀ φ] ↔ ⇓LTL[N.ampleModel lvl V,M₀ ⊨∀ φ] :=
  allPaths_reduced_iff ampleSelector_isAmple (ampleSelector_cycleProviso hB)
    (fun s μ s' p hp h hi => hS s μ s' p hp h hi) hφ hφS

/-- **Partial-order reduction of executable nets preserves LTL without next-time on some path.** -/
theorem somePath_ampleModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {S : Set (Atom Place Transition)}
    (hS : ∀ M t M' a, a ∈ S → M [t⟩[N] M' → t ∉ V → (N.model.v M a ↔ N.model.v M' a))
    {φ : Formula (Atom Place Transition)} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[N.model,M₀ ⊨∃ φ] ↔ ⇓LTL[N.ampleModel lvl V,M₀ ⊨∃ φ] :=
  somePath_reduced_iff ampleSelector_isAmple (ampleSelector_cycleProviso hB)
    (fun s μ s' p hp h hi => hS s μ s' p hp h hi) hφ hφS

end ExecPetriNet

end Cslib
