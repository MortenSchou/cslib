/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableAmpleLTL

/-! # Partial-order reduction for LTL over the tokens of places

The atoms of `Cslib.Computability.PetriNets.CTL` say that the marking is exactly a given marking
or that a transition is enabled, and few transitions leave them unchanged. Properties of nets are
often about the tokens of a few places instead. This file gives the atoms `k ≤ M p` of a place `p`,
and an LTL model of the marking graph over them. Formulas over the places in a finite set `P`
are preserved by the partial-order reduction with the visible transitions
`ExecPetriNet.visibleOf P`, the transitions that change the tokens of some place of `P`. All other
transitions are invisible and the reduction can postpone them.

The atom `M p = k` is the conjunction of `k ≤ M p` and the negation of `k + 1 ≤ M p`, so that
threshold atoms suffice.

## Main definitions

- `PetriNet.PlaceAtom`: the atom `k ≤ M p`.
- `PetriNet.placeModel`: the marking graph as a model over the atoms of places.
- `ExecPetriNet.amplePlaceModel`: the marking graph restricted to the transitions selected by
  `ExecPetriNet.ampleSelector`, as a model over the atoms of places.

## Main statements

- `ExecPetriNet.allPaths_placeModel_iff`, `ExecPetriNet.somePath_placeModel_iff`: a formula without
  next-time over the atoms of places in `P` holds on all, respectively some, maximal firing
  sequences iff it does in the reduced graph, if the transitions with a net effect on `P` are
  visible and the level function is bounded on the reduced reachable markings.
- `ExecPetriNet.exists_mem_ampleReachSet_of_isPath`: a maximal path of the reduced model stays in
  a closed level of `ExecPetriNet.ampleReachSet`, so that safety formulas can be checked on the
  finite set, for example by `decide`.
-/

@[expose] public section

namespace Cslib

open Cslib.Logic Cslib.Logic.LTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL

namespace PetriNet

/-- The atom `k ≤ M p`: the place `p` holds at least `k` tokens. -/
structure PlaceAtom (Place : Type*) where
  /-- The place. -/
  place : Place
  /-- The threshold. -/
  threshold : ℕ

/-- The marking graph of a net as a model over the atoms of places. -/
def placeModel {Place Transition : Type*} (N : PetriNet Place Transition) :
    CTL.Model (Marking Place) (PlaceAtom Place) :=
  ⟨N.lts, fun M a => a.threshold ≤ M a.place⟩

end PetriNet

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

variable {Place Transition : Type*} [LinearOrder Place] [LinearOrder Transition]
  [Fintype Transition] (N : ExecPetriNet Place Transition)

/-- The marking graph restricted to the transitions selected by `ampleSelector`, as a model over the
atoms of places. -/
def amplePlaceModel (lvl : Multiset Place → ℕ) (V : Finset Transition) :
    CTL.Model (Marking Place) (PlaceAtom Place) :=
  ⟨N.toPetriNet.lts.reduced (N.ampleSelector lvl V), N.toPetriNet.placeModel.v⟩

variable {N} {lvl : Multiset Place → ℕ} {V : Finset Transition}

omit [LinearOrder Transition] in
/-- The atoms of the places in `P` are not changed by the transitions outside the visible
transitions of `P`. -/
theorem placeAtoms_invisible {P : Finset Place} (hV : N.visibleOf P ⊆ V) :
    ∀ M t M' a, a ∈ {a : PlaceAtom Place | a.place ∈ P} → M [t⟩[N] M' → t ∉ V →
      (N.toPetriNet.placeModel.v M a ↔ N.toPetriNet.placeModel.v M' a) := by
  intro M t M' a ha h ht
  change _ ≤ _ ↔ _ ≤ _
  rw [apply_eq_of_not_mem_visibleOf h (fun hv => ht (hV hv)) ha]

/-- **Partial-order reduction preserves LTL over the tokens of places, on all paths.** A formula
without next-time whose atoms are over the places in `P` holds on all maximal firing sequences from
a marking iff it does in the reduced graph, if `V` contains the transitions with a net effect on a
place of `P`, and the level function is bounded on the reduced reachable markings. -/
theorem allPaths_placeModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Finset Place} (hV : N.visibleOf P ⊆ V) {φ : Formula (PlaceAtom Place)}
    (hφ : φ.NextFree) (hφP : φ.atomSet ⊆ {a | a.place ∈ P}) :
    ⇓LTL[N.toPetriNet.placeModel,M₀ ⊨∀ φ] ↔ ⇓LTL[N.amplePlaceModel lvl V,M₀ ⊨∀ φ] :=
  allPaths_reduced_iff ampleSelector_isAmple (ampleSelector_cycleProviso hB)
    (fun s μ s' p hp h hi => placeAtoms_invisible hV s μ s' p hp h hi) hφ hφP

/-- **Partial-order reduction preserves LTL over the tokens of places, on some path.** -/
theorem somePath_placeModel_iff {M₀ : Marking Place} {B : ℕ} (hB : N.LevelBounded lvl V B M₀)
    {P : Finset Place} (hV : N.visibleOf P ⊆ V) {φ : Formula (PlaceAtom Place)}
    (hφ : φ.NextFree) (hφP : φ.atomSet ⊆ {a | a.place ∈ P}) :
    ⇓LTL[N.toPetriNet.placeModel,M₀ ⊨∃ φ] ↔ ⇓LTL[N.amplePlaceModel lvl V,M₀ ⊨∃ φ] :=
  somePath_reduced_iff ampleSelector_isAmple (ampleSelector_cycleProviso hB)
    (fun s μ s' p hp h hi => placeAtoms_invisible hV s μ s' p hp h hi) hφ hφP

/-- A maximal path of the reduced model that starts at `M₀` stays in a closed level of
`ampleReachSet`. -/
theorem exists_mem_ampleReachSet_of_isPath {M₀ : Multiset Place} {n : ℕ}
    (hc : N.AmpleClosed lvl V M₀ n) {f : ℕ → Marking Place}
    (hf : (N.amplePlaceModel lvl V).IsPath f) (h0 : f 0 = Multiset.toFinsupp M₀) (k : ℕ) :
    ∃ m ∈ N.ampleReachSet lvl V M₀ n, f k = Multiset.toFinsupp m := by
  induction k with
  | zero => exact ⟨M₀, mem_reducedReachSet_self n, h0⟩
  | succ k ih =>
    obtain ⟨m, hm, hk⟩ := ih
    rcases hf k with ⟨μ, htr⟩ | ⟨-, heq⟩
    · exact mem_of_reduced_mTr hc (.single _ htr) m hm hk
    · exact ⟨m, hm, heq.trans hk⟩

end ExecPetriNet

end Cslib
