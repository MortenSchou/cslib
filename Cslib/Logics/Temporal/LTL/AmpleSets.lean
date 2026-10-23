/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Semantics.LTS.AmplePaths
public import Cslib.Logics.Temporal.LTL.Model
public import Cslib.Logics.Temporal.LTL.Stuttering

/-! # Partial-order reduction preserves LTL without next-time

An ample selector with the cycle proviso (`Cslib.Foundations.Semantics.LTS.AmpleSets`) selects at
each state of a deterministic LTS a subset of the labels. A formula of LTL without the next-time
operator `X` holds on all maximal paths of the LTS iff it holds on all maximal paths of the
reduced LTS, and on some maximal path of the LTS iff on some maximal path of the reduced LTS. This
is the theorem of Peled that partial-order reduction preserves LTL without next-time.

The conditions on the selector are `LTS.IsAmple` (`C0`, `C1`, `C2`) and `LTS.CycleProviso` (`C3`).
For the formula `φ`, the labels `Inv` that `C2` takes to be invisible must not change the atoms of
`φ`, as in the hypothesis `hS`. Finite and infinite maximal paths are both covered, with the
stuttering at a terminal state of `Model.IsPath`. The proof combines
`LTS.forall_isMaxPath_iff_reduced` and `LTS.exists_isMaxPath_iff_reduced`, which hold for any
property of the sequence of observations that is invariant under stuttering, with the invariance of
next-free formulas under stuttering equivalence, `Satisfies.iff_of_stutterEq`.

The LTS need not be deterministic if the selector satisfies the stepwise stubbornness of
`LTS.IsAmpleStep` (`allPaths_reduced_iff_of_isAmpleStep`); for a deterministic LTS, such as a
marking graph, `LTS.IsAmple` suffices (`allPaths_reduced_iff`). The labels and atoms
need no other assumption: the formula `φ` may mention only the atoms `S` that the invisible labels
preserve.

## Main statements

- `LTL.allPaths_reduced_iff`: preservation of `⊨∀`.
- `LTL.somePath_reduced_iff`: preservation of `⊨∃`.
- `LTL.allPaths_reduced_iff_of_isAmpleStep`, `LTL.somePath_reduced_iff_of_isAmpleStep`: the same
  for LTSs that are not deterministic.

## References

* [D. Peled, *All from one, one for all: on model checking using representatives*][Peled1993]
-/

@[expose] public section

namespace Cslib.Logic.LTL

open Cslib Cslib.ωSequence Cslib.LTS
open scoped InferenceSystem CTL

variable {State : Type*} {Label : Type*} {Atom : Type*} {lts : LTS State Label}
  {v : State → Atom → Prop}

/-- The maximal paths of the model of an LTS are its maximal paths. -/
theorem isPath_iff_isMaxPath {f : ℕ → State} :
    CTL.Model.IsPath (⟨lts, v⟩ : CTL.Model State Atom) f ↔ lts.IsMaxPath f := by
  have hdead : ∀ s, CTL.Model.Dead (⟨lts, v⟩ : CTL.Model State Atom) s ↔ lts.IsTerminal s :=
    fun s => ⟨fun h μ s' htr => h s' ⟨μ, htr⟩, fun h t ⟨μ, htr⟩ => h μ t htr⟩
  exact forall_congr' fun n => or_congr Iff.rfl (and_congr (hdead _) Iff.rfl)

section Reduction

variable {A : State → Set Label} {Inv : Label → Prop}

/-- A formula holds on all maximal paths from `s` of a model iff it holds on the sequences of the
atoms in `S` that hold on all maximal paths, if `S` contains the atoms of the formula. -/
private theorem allPaths_iff_map {lts' : LTS State Label} {S : Set Atom} {φ : Formula Atom}
    (hφS : φ.atomSet ⊆ S) {s : State} :
    ⇓LTL[(⟨lts', v⟩ : CTL.Model State Atom),s ⊨∀ φ] ↔ ∀ f : ℕ → State, lts'.IsMaxPath f →
      f 0 = s → Satisfies ((f : ωSequence State).map fun s => {p | v s p} ∩ S) φ :=
  forall_congr' fun _ => imp_congr isPath_iff_isMaxPath <|
    imp_congr_right fun _ => Satisfies.iff_map_inter hφS

/-- The existential version of `allPaths_iff_map`. -/
private theorem somePath_iff_map {lts' : LTS State Label} {S : Set Atom} {φ : Formula Atom}
    (hφS : φ.atomSet ⊆ S) {s : State} :
    ⇓LTL[(⟨lts', v⟩ : CTL.Model State Atom),s ⊨∃ φ] ↔ ∃ f : ℕ → State, lts'.IsMaxPath f ∧
      f 0 = s ∧ Satisfies ((f : ωSequence State).map fun s => {p | v s p} ∩ S) φ :=
  exists_congr fun _ => and_congr isPath_iff_isMaxPath <|
    and_congr_right fun _ => Satisfies.iff_map_inter hφS

/-- The observation of the atoms in `S` is not changed by the invisible labels. -/
private theorem observation_eq {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p)) (s : State)
    (μ : Label) (s' : State) (htr : lts.Tr s μ s') (hi : Inv μ) :
    {p | v s p} ∩ S = {p | v s' p} ∩ S :=
  Set.ext fun p => and_congr_left fun hp => hS s μ s' p hp htr hi

/-- **Partial-order reduction preserves LTL without next-time on all paths, for LTSs that are not
deterministic.** A formula without next-time, whose atoms are not changed by the invisible labels,
holds on all maximal paths from a state of the model iff it does in the model reduced by a
stepwise ample selector with the cycle proviso. -/
theorem allPaths_reduced_iff_of_isAmpleStep {s : State} (hA : lts.IsAmpleStep A Inv)
    (h3 : lts.CycleProviso A s) {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p))
    {φ : Formula Atom} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[(⟨lts, v⟩ : CTL.Model State Atom),s ⊨∀ φ] ↔
      ⇓LTL[(⟨lts.reduced A, v⟩ : CTL.Model State Atom),s ⊨∀ φ] :=
  (allPaths_iff_map hφS).trans <|
    (hA.forall_isMaxPath_iff_reduced h3 (observation_eq hS) (P := fun w => Satisfies w φ)
      (Satisfies.iff_of_stutterEq hφ)).trans (allPaths_iff_map hφS).symm

/-- The existential version of `allPaths_reduced_iff_of_isAmpleStep`. -/
theorem somePath_reduced_iff_of_isAmpleStep {s : State} (hA : lts.IsAmpleStep A Inv)
    (h3 : lts.CycleProviso A s) {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p))
    {φ : Formula Atom} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[(⟨lts, v⟩ : CTL.Model State Atom),s ⊨∃ φ] ↔
      ⇓LTL[(⟨lts.reduced A, v⟩ : CTL.Model State Atom),s ⊨∃ φ] :=
  (somePath_iff_map hφS).trans <|
    (hA.exists_isMaxPath_iff_reduced h3 (observation_eq hS) (P := fun w => Satisfies w φ)
      (Satisfies.iff_of_stutterEq hφ)).trans (somePath_iff_map hφS).symm

/-- **Partial-order reduction preserves LTL without next-time on all paths.** A formula without
next-time, whose atoms are not changed by the invisible labels, holds on all maximal paths from a
state of the model iff it does in the reduced model. -/
theorem allPaths_reduced_iff [lts.Deterministic] {s : State} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p))
    {φ : Formula Atom} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[(⟨lts, v⟩ : CTL.Model State Atom),s ⊨∀ φ] ↔
      ⇓LTL[(⟨lts.reduced A, v⟩ : CTL.Model State Atom),s ⊨∀ φ] :=
  allPaths_reduced_iff_of_isAmpleStep hA.toIsAmpleStep h3 hS hφ hφS

/-- **Partial-order reduction preserves LTL without next-time on some path.** The same as
`allPaths_reduced_iff` for the existence of a maximal path. -/
theorem somePath_reduced_iff [lts.Deterministic] {s : State} (hA : lts.IsAmple A Inv)
    (h3 : lts.CycleProviso A s) {S : Set Atom}
    (hS : ∀ s μ s' p, p ∈ S → lts.Tr s μ s' → Inv μ → (v s p ↔ v s' p))
    {φ : Formula Atom} (hφ : φ.NextFree) (hφS : φ.atomSet ⊆ S) :
    ⇓LTL[(⟨lts, v⟩ : CTL.Model State Atom),s ⊨∃ φ] ↔
      ⇓LTL[(⟨lts.reduced A, v⟩ : CTL.Model State Atom),s ⊨∃ φ] :=
  somePath_reduced_iff_of_isAmpleStep hA.toIsAmpleStep h3 hS hφ hφS

end Reduction

end Cslib.Logic.LTL
