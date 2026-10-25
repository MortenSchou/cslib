/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.AmpleLTL

/-! # Partial-order reduction for LTL over the tokens of places

The atoms of `Cslib.Computability.PetriNets.CTL` say that the marking is exactly a given marking
or that a transition is enabled, and few transitions leave them unchanged. Properties of nets are
often about the tokens of a few places instead. This file gives the atoms `k ≤ M.count p` of a
place `p`, and an LTL model of the marking graph over them. Formulas over the places in a finite set
`P` are preserved by the partial-order reduction with the visible transitions
`PetriNet.visibleOf P`, the transitions that change the tokens of some place of `P`. All other
transitions are invisible and the reduction can postpone them.

The atom `M.count p = k` is the conjunction of `k ≤ M.count p` and the negation of
`k + 1 ≤ M.count p`, so that threshold atoms suffice.

## Main definitions

- `PetriNet.PlaceAtom`: the atom `k ≤ M.count p`.
- `PetriNet.placeModel`: the marking graph as a model over the atoms of places.
- `PetriNet.amplePlaceModel`: the marking graph restricted to the transitions selected by
  `PetriNet.ampleFinset`, as a model over the atoms of places.

## Main statements

- `PetriNet.allPaths_placeModel_iff`, `PetriNet.somePath_placeModel_iff`: a formula without
  next-time over the atoms of places in `P` holds on all, respectively some, maximal firing
  sequences iff it does in the reduced graph, if the transitions with a net effect on `P` are
  visible and the level function is bounded on the reduced reachable markings.
- `PetriNet.mem_ampleReachSet_of_isPath`: a maximal path of the reduced model stays in a closed
  level of `PetriNet.ampleReachSet`, so that safety formulas can be checked on the finite set, for
  example by `decide`.
-/

@[expose] public section

namespace Cslib

open Cslib.Logic Cslib.Logic.LTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL

namespace PetriNet

/-- The atom `k ≤ M.count p`: the place `p` holds at least `k` tokens. -/
structure PlaceAtom (Place : Type*) where
  /-- The place. -/
  place : Place
  /-- The threshold. -/
  threshold : ℕ

/-- The marking graph of a net as a model over the atoms of places. -/
def placeModel {Place Transition : Type*} [DecidableEq Place] (N : PetriNet Place Transition) :
    CTL.Model (Marking Place) (PlaceAtom Place) :=
  ⟨N.lts, fun M a => a.threshold ≤ M.count a.place⟩

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : PetriNet Place Transition)

/-- The marking graph restricted to the transitions selected by `ampleFinset`, as a model over the
atoms of places. -/
def amplePlaceModel (lvl : Marking Place → ℕ) (V : Finset Transition) :
    CTL.Model (Marking Place) (PlaceAtom Place) :=
  ⟨N.reduced (N.ampleFinset lvl V ·), N.placeModel.v⟩

variable {N} {lvl : Marking Place → ℕ} {V : Finset Transition}

omit [LinearOrder Transition] in
/-- The atoms of the places in `P` are not changed by the transitions outside the visible
transitions of `P`. -/
theorem placeAtoms_invisible {P : Finset Place} (hV : N.visibleOf P ⊆ V) :
    ∀ M t M' a, a ∈ {a : PlaceAtom Place | a.place ∈ P} → M [t⟩[N] M' → t ∉ V →
      (N.placeModel.v M a ↔ N.placeModel.v M' a) := by
  intro M t M' a ha h ht
  change _ ≤ _ ↔ _ ≤ _
  rw [count_eq_of_notMem_visibleOf h (fun hv => ht (hV hv)) ha]

/-- **Partial-order reduction preserves LTL over the tokens of places, on all paths.** A formula
without next-time whose atoms are over the places in `P` holds on all maximal firing sequences from
a marking iff it does in the reduced graph, if `V` contains the transitions with a net effect on a
place of `P`, and the level function is bounded on the reduced reachable markings. -/
theorem allPaths_placeModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Finset Place} (hV : N.visibleOf P ⊆ V) {φ : Formula (PlaceAtom Place)}
    (hφ : φ.NextFree) (hφP : φ.atomSet ⊆ {a | a.place ∈ P}) :
    ⇓LTL[N.placeModel,M₀ ⊨∀ φ] ↔ ⇓LTL[N.amplePlaceModel lvl V,M₀ ⊨∀ φ] :=
  allPaths_reduced_iff ampleFinset_isAmple (ampleFinset_cycleProviso hB)
    (fun s μ s' p hp h hi => placeAtoms_invisible hV s μ s' p hp h hi) hφ hφP

/-- **Partial-order reduction preserves LTL over the tokens of places, on some path.** -/
theorem somePath_placeModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Finset Place} (hV : N.visibleOf P ⊆ V) {φ : Formula (PlaceAtom Place)}
    (hφ : φ.NextFree) (hφP : φ.atomSet ⊆ {a | a.place ∈ P}) :
    ⇓LTL[N.placeModel,M₀ ⊨∃ φ] ↔ ⇓LTL[N.amplePlaceModel lvl V,M₀ ⊨∃ φ] :=
  somePath_reduced_iff ampleFinset_isAmple (ampleFinset_cycleProviso hB)
    (fun s μ s' p hp h hi => placeAtoms_invisible hV s μ s' p hp h hi) hφ hφP

/-- A maximal path of the reduced model that starts at `M₀` stays in a closed level of
`ampleReachSet`. -/
theorem mem_ampleReachSet_of_isPath {M₀ : Marking Place} {n : ℕ}
    (hc : N.AmpleClosed lvl V M₀ n) {f : ℕ → Marking Place}
    (hf : (N.amplePlaceModel lvl V).IsPath f) (h0 : f 0 = M₀) (k : ℕ) :
    f k ∈ N.ampleReachSet lvl V M₀ n := by
  induction k with
  | zero => exact h0 ▸ mem_reducedReachSet_self n
  | succ k ih =>
    rcases hf k with ⟨μ, htr⟩ | ⟨-, heq⟩
    · exact mem_of_reduced_mTr hc (.single _ htr) ih
    · exact heq ▸ ih

end PetriNet

end Cslib
