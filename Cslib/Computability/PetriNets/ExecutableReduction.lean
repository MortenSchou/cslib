/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Executable
public import Cslib.Computability.PetriNets.ReducesTo

/-! # Executable reductions

The reductions of nets, as operations on executable nets, with proofs that they agree with the
reductions of weighted nets, and decidable side conditions. The reduced net is again an executable
net, over places and transitions that are subtypes of the original ones, so the decision procedures
for executable nets apply to it. Together with the certificates `PetriNet.ReducesTo` and
`PetriNet.ReducesWF`, this lets a question about a net be decided on a smaller net (see
`Cslib.Computability.PetriNets.ExecutableReducedDecisions`).

## Main definitions

- `ExecPetriNet.removePlace`, `ExecPetriNet.removeTransition`, `ExecPetriNet.fuseDelete`: the
  reduced nets. `ExecPetriNet.toPetriNet_removePlace`, `ExecPetriNet.toPetriNet_removeTransition`
  and `ExecPetriNet.toPetriNet_fuseDelete` relate them to `PetriNet.removePlace`,
  `PetriNet.removeTransition` and `PetriNet.fuseDelete`.
- `ExecPetriNet.dropMarking`, `ExecPetriNet.collapseMarking`: the corresponding operations on
  multiset markings, related to `PetriNet.Marking.drop` and `PetriNet.collapse` by
  `ExecPetriNet.toFinsupp_dropMarking` and `ExecPetriNet.toFinsupp_collapseMarking`.
- `ExecPetriNet.rename`, `ExecPetriNet.renamePlaces`, `ExecPetriNet.renameTransitions`: renaming
  the places and the transitions, or only the places, or only the transitions.
- `ExecPetriNet.ReducesTo`, `ExecPetriNet.ReducesWF`: the certificates of `PetriNet.ReducesTo` and
  `PetriNet.ReducesWF`, for executable nets and multiset markings, with a theorem for each rule
  whose side conditions are stated for multisets.

## Decidable side conditions

The predicates `IsDrain`, `IsSeries`, `IsSeriesPlace`, `ParallelTransitions`, `ParallelPlaces` and
`IsIsolated` of weighted nets are decidable on `N.toPetriNet` for an executable net `N` over
finitely many transitions (instances below), with the iff-lemmas `ExecPetriNet.isDrain_iff` etc.
that state them for multisets. Redundancy of a place is not checked in general; the rules use the
sufficient conditions of self-loop places, parallel places and isolated places instead. Likewise
the elimination of a self-loop transition needs side conditions on deadlocks and liveness that are
not checked; `ExecPetriNet.ReducesTo.selfLoopTransition_of_twin` uses a sufficient, decidable
condition.

Reductions of places and of transitions only make the net smaller: they do not change the set of
reachable markings (up to forgetting the place). Fusion of a drained place also reduces the number
of reachable markings.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

universe u v

section Marking

variable {Place : Type*} [DecidableEq Place]

/-- A multiset marking restricted to the places other than `p`. -/
def dropMarking (p : Place) (M : Multiset Place) : Multiset {q // q ≠ p} :=
  M.filterMap fun q => if h : q ≠ p then some ⟨q, h⟩ else none

theorem dropMarking_cons_self (p : Place) (M : Multiset Place) :
    dropMarking p (p ::ₘ M) = dropMarking p M :=
  Multiset.filterMap_cons_none _ _ (by simp)

theorem dropMarking_cons_of_ne {p a : Place} (h : a ≠ p) (M : Multiset Place) :
    dropMarking p (a ::ₘ M) = ⟨a, h⟩ ::ₘ dropMarking p M :=
  Multiset.filterMap_cons_some _ _ _ (by simp [h])

@[simp] theorem count_dropMarking (p : Place) (M : Multiset Place) (q : {q // q ≠ p}) :
    (dropMarking p M).count q = M.count q.1 := by
  induction M using Multiset.induction with
  | empty => simp [dropMarking]
  | cons a M ih =>
    by_cases h : a = p
    · subst h
      rw [dropMarking_cons_self, ih, Multiset.count_cons]
      simp [q.2]
    · rw [dropMarking_cons_of_ne h, Multiset.count_cons, ih, Multiset.count_cons]
      simp [Subtype.ext_iff, eq_comm]

/-- Restricting a multiset marking is restricting the marking it denotes. -/
theorem toFinsupp_dropMarking (p : Place) (M : Multiset Place) :
    Multiset.toFinsupp (dropMarking p M) = Marking.drop p (Multiset.toFinsupp M) := by
  ext q
  simp [Multiset.toFinsupp_apply]

end Marking

section Nets

variable {Place Transition : Type*} [DecidableEq Place] (N : ExecPetriNet Place Transition)

/-- The net with the place `p` deleted. -/
def removePlace (p : Place) : ExecPetriNet {q // q ≠ p} Transition where
  pre t := dropMarking p (N.pre t)
  post t := dropMarking p (N.post t)

/-- The net with the transition `t₂` deleted. -/
def removeTransition (t₂ : Transition) : ExecPetriNet Place {t // t ≠ t₂} where
  pre t := N.pre t.1
  post t := N.post t.1

/-- The multiset marking in which every token of `p` has been replaced by a copy of the postset of
`t₂`. -/
def collapseMarking (t₂ : Transition) (p : Place) (M : Multiset Place) : Multiset Place :=
  M.filter (· ≠ p) + M.count p • N.post t₂

/-- Fusing the series with the transition `t₂` that drains `p`: the transition `t₂` and the place
`p` are deleted, and the tokens that a transition puts in `p` are replaced by the postset of
`t₂`. -/
def fuseDelete (t₂ : Transition) (p : Place) : ExecPetriNet {q // q ≠ p} {t // t ≠ t₂} where
  pre t := dropMarking p (N.pre t.1)
  post t := dropMarking p (N.collapseMarking t₂ p (N.post t.1))

variable {N}

/-- Deleting a place from an executable net is deleting it from the weighted net. -/
theorem toPetriNet_removePlace (p : Place) :
    (N.removePlace p).toPetriNet = N.toPetriNet.removePlace p := by
  change PetriNet.mk _ _ = PetriNet.mk _ _
  congr 1 <;> funext t <;> exact toFinsupp_dropMarking _ _

/-- Deleting a transition from an executable net is deleting it from the weighted net. -/
theorem toPetriNet_removeTransition (t₂ : Transition) :
    (N.removeTransition t₂).toPetriNet = N.toPetriNet.removeTransition t₂ := rfl

/-- Collapsing a multiset marking is collapsing the marking it denotes. -/
theorem toFinsupp_collapseMarking (t₂ : Transition) (p : Place) (M : Multiset Place) :
    Multiset.toFinsupp (N.collapseMarking t₂ p M) =
      N.toPetriNet.collapse t₂ p (Multiset.toFinsupp M) := by
  ext q
  by_cases hq : q = p
  · subst hq
    simp [collapseMarking, collapse, toPetriNet, Multiset.toFinsupp_apply]
  · simp [collapseMarking, collapse, toPetriNet, Multiset.toFinsupp_apply, hq]

/-- Fusing and deleting in an executable net is fusing and deleting in the weighted net. -/
theorem toPetriNet_fuseDelete (t₂ : Transition) (p : Place) :
    (N.fuseDelete t₂ p).toPetriNet = N.toPetriNet.fuseDelete t₂ p := by
  change PetriNet.mk _ _ = PetriNet.mk _ _
  congr 1 <;> funext t
  · exact toFinsupp_dropMarking _ _
  · exact (toFinsupp_dropMarking _ _).trans (congrArg _ (toFinsupp_collapseMarking _ _ _))

end Nets

/-! ### Renaming -/

section Rename

variable {Place Place' Transition Transition' : Type*} [DecidableEq Place] [DecidableEq Place']

/-- Renaming a multiset marking is renaming the marking it denotes. -/
theorem toFinsupp_map (e : Place ≃ Place') (M : Multiset Place) :
    Multiset.toFinsupp (M.map e) = Marking.rename e (Multiset.toFinsupp M) := by
  ext q
  simp only [Multiset.toFinsupp_apply, Marking.rename_apply]
  have := Multiset.count_map_eq_count' e M e.injective (e.symm q)
  rwa [Equiv.apply_symm_apply] at this

/-- The net with the places renamed along `e` and the transitions along `f`. -/
def rename (N : ExecPetriNet Place Transition) (e : Place ≃ Place') (f : Transition ≃ Transition') :
    ExecPetriNet Place' Transition' where
  pre t := (N.pre (f.symm t)).map e
  post t := (N.post (f.symm t)).map e

/-- Renaming an executable net is renaming the weighted net. -/
theorem toPetriNet_rename (N : ExecPetriNet Place Transition) (e : Place ≃ Place')
    (f : Transition ≃ Transition') :
    (N.rename e f).toPetriNet = N.toPetriNet.rename e f := by
  change PetriNet.mk _ _ = PetriNet.mk _ _
  congr 1 <;> funext t <;> exact toFinsupp_map _ _

/-- The net with the places renamed along `e`. -/
def renamePlaces (N : ExecPetriNet Place Transition) (e : Place ≃ Place') :
    ExecPetriNet Place' Transition where
  pre t := (N.pre t).map e
  post t := (N.post t).map e

/-- The net with the transitions renamed along `f`. -/
def renameTransitions (N : ExecPetriNet Place Transition) (f : Transition ≃ Transition') :
    ExecPetriNet Place Transition' where
  pre t := N.pre (f.symm t)
  post t := N.post (f.symm t)

/-- Renaming the places of an executable net is renaming the places of the weighted net. -/
theorem toPetriNet_renamePlaces (N : ExecPetriNet Place Transition) (e : Place ≃ Place') :
    (N.renamePlaces e).toPetriNet = N.toPetriNet.rename e (Equiv.refl Transition) := by
  change PetriNet.mk _ _ = PetriNet.mk _ _
  congr 1 <;> funext t <;> exact toFinsupp_map _ _

/-- Renaming the transitions of an executable net is renaming the transitions of the weighted
net. -/
theorem toPetriNet_renameTransitions (N : ExecPetriNet Place Transition)
    (f : Transition ≃ Transition') :
    (N.renameTransitions f).toPetriNet = N.toPetriNet.rename (Equiv.refl Place) f := by
  change PetriNet.mk _ _ = PetriNet.mk _ _
  congr 1 <;> funext t <;> exact (Marking.rename_refl _).symm

end Rename

/-! ### Decidable side conditions -/

section Structure

variable {Place Transition : Type*} [DecidableEq Place] {N : ExecPetriNet Place Transition}

@[simp] theorem pre_apply (t : Transition) (p : Place) :
    (N.toPetriNet.pre t) p = (N.pre t).count p := Multiset.toFinsupp_apply _ _

@[simp] theorem post_apply (t : Transition) (p : Place) :
    (N.toPetriNet.post t) p = (N.post t).count p := Multiset.toFinsupp_apply _ _

theorem toFinsupp_eq_single_iff {m : Multiset Place} {p : Place} :
    Multiset.toFinsupp m = Finsupp.single p 1 ↔ m = {p} := by
  rw [← Multiset.toFinsupp_singleton]
  exact Multiset.toFinsupp.injective.eq_iff

/-- `t` drains `p`, stated for multisets. -/
theorem isDrain_iff {t : Transition} {p : Place} :
    N.toPetriNet.IsDrain t p ↔
      N.pre t = {p} ∧ (N.post t).count p = 0 ∧ ∀ t', t' ≠ t → (N.pre t').count p = 0 := by
  constructor
  · intro h
    refine ⟨toFinsupp_eq_single_iff.1 h.pre_eq, ?_, fun t' ht' => ?_⟩
    · simpa using h.post_apply
    · simpa using h.pre_of_ne t' ht'
  · rintro ⟨h₁, h₂, h₃⟩
    exact ⟨toFinsupp_eq_single_iff.2 h₁, by simpa using h₂, fun t' ht' => by simpa using h₃ t' ht'⟩

/-- `t₁ → p → t₂` is a series of transitions, stated for multisets. -/
theorem isSeries_iff {t₁ t₂ : Transition} {p : Place} :
    N.toPetriNet.IsSeries t₁ t₂ p ↔ N.toPetriNet.IsDrain t₂ p ∧ (N.post t₁).count p = 1 :=
  ⟨fun h => ⟨h.toIsDrain, by simpa using h.post_left⟩,
    fun ⟨h₁, h₂⟩ => ⟨h₁, by simpa using h₂⟩⟩

/-- `p₁ → t → p₂` is a series of places, stated for multisets. -/
theorem isSeriesPlace_iff {t : Transition} {p₁ p₂ : Place} :
    N.toPetriNet.IsSeriesPlace t p₁ p₂ ↔
      p₁ ≠ p₂ ∧ N.pre t = {p₁} ∧ N.post t = {p₂} ∧ ∀ t', t' ≠ t → (N.pre t').count p₁ = 0 := by
  constructor
  · intro h
    exact ⟨h.ne, toFinsupp_eq_single_iff.1 h.pre_eq, toFinsupp_eq_single_iff.1 h.post_eq,
      fun t' ht' => by simpa using h.pre_of_ne t' ht'⟩
  · rintro ⟨h₀, h₁, h₂, h₃⟩
    exact ⟨h₀, toFinsupp_eq_single_iff.2 h₁, toFinsupp_eq_single_iff.2 h₂,
      fun t' ht' => by simpa using h₃ t' ht'⟩

/-- Two transitions are parallel, stated for multisets. -/
theorem parallelTransitions_iff {t₁ t₂ : Transition} :
    N.toPetriNet.ParallelTransitions t₁ t₂ ↔
      t₁ ≠ t₂ ∧ N.pre t₁ = N.pre t₂ ∧ N.post t₁ = N.post t₂ := by
  simp only [PetriNet.ParallelTransitions, toPetriNet, Multiset.toFinsupp.injective.eq_iff]

/-- Two places are parallel, stated for multisets. -/
theorem parallelPlaces_iff {p q : Place} :
    N.toPetriNet.ParallelPlaces p q ↔
      p ≠ q ∧ (∀ t, (N.pre t).count p = (N.pre t).count q) ∧
        ∀ t, (N.post t).count p = (N.post t).count q := by
  simp only [PetriNet.ParallelPlaces, pre_apply, post_apply]

/-- A place is isolated, stated for multisets. -/
theorem isIsolated_iff {p : Place} :
    N.toPetriNet.IsIsolated p ↔ ∀ t, (N.pre t).count p = 0 ∧ (N.post t).count p = 0 := by
  simp only [PetriNet.IsIsolated, pre_apply, post_apply]

/-- `t` is a self-loop transition, stated for multisets. -/
theorem isSelfLoopTransition_iff {t : Transition} :
    N.toPetriNet.IsSelfLoopTransition t ↔ N.pre t = N.post t :=
  Multiset.toFinsupp.injective.eq_iff

instance {t : Transition} : Decidable (N.toPetriNet.IsSelfLoopTransition t) :=
  decidable_of_iff _ isSelfLoopTransition_iff.symm

instance [DecidableEq Transition] [Fintype Transition] {t : Transition} {p : Place} :
    Decidable (N.toPetriNet.IsDrain t p) :=
  decidable_of_iff _ isDrain_iff.symm

instance [DecidableEq Transition] [Fintype Transition] {t₁ t₂ : Transition} {p : Place} :
    Decidable (N.toPetriNet.IsSeries t₁ t₂ p) :=
  decidable_of_iff _ isSeries_iff.symm

instance [DecidableEq Transition] [Fintype Transition] {t : Transition} {p₁ p₂ : Place} :
    Decidable (N.toPetriNet.IsSeriesPlace t p₁ p₂) :=
  decidable_of_iff _ isSeriesPlace_iff.symm

instance [DecidableEq Transition] {t₁ t₂ : Transition} :
    Decidable (N.toPetriNet.ParallelTransitions t₁ t₂) :=
  decidable_of_iff _ parallelTransitions_iff.symm

instance [Fintype Transition] {p q : Place} : Decidable (N.toPetriNet.ParallelPlaces p q) :=
  decidable_of_iff _ parallelPlaces_iff.symm

instance [Fintype Transition] {p : Place} : Decidable (N.toPetriNet.IsIsolated p) :=
  decidable_of_iff _ isIsolated_iff.symm

end Structure

/-! ### Certificates for executable nets -/

/-- `N.ReducesTo M₀ N' M₀'` says that the executable net `N'` with initial marking `M₀'` is
obtained from `N` with `M₀` by Murata's reductions; it is `PetriNet.ReducesTo` for the weighted
nets and the markings that they denote. -/
def ReducesTo {Place Place' : Type u} {Transition Transition' : Type v}
    [DecidableEq Place] [DecidableEq Place'] (N : ExecPetriNet Place Transition)
    (M₀ : Multiset Place) (N' : ExecPetriNet Place' Transition') (M₀' : Multiset Place') : Prop :=
  PetriNet.ReducesTo N.toPetriNet (Multiset.toFinsupp M₀) N'.toPetriNet (Multiset.toFinsupp M₀')

/-- `N.ReducesWF i o N' i' o'` says that the workflow net `N'` with source `i'` and sink `o'` is
obtained from `N` with source `i` and sink `o` by fusing series; it is `PetriNet.ReducesWF` for the
weighted nets. -/
def ReducesWF {Place Place' : Type u} {Transition Transition' : Type v}
    [DecidableEq Place] [DecidableEq Place'] (N : ExecPetriNet Place Transition) (i o : Place)
    (N' : ExecPetriNet Place' Transition') (i' o' : Place') : Prop :=
  PetriNet.ReducesWF N.toPetriNet i o N'.toPetriNet i' o'

namespace ReducesTo

section Rules

variable {Place : Type u} {Transition : Type v} [DecidableEq Place]
  {N : ExecPetriNet Place Transition} {M₀ : Multiset Place}

/-- The empty reduction. -/
theorem refl (N : ExecPetriNet Place Transition) (M₀ : Multiset Place) : N.ReducesTo M₀ N M₀ :=
  PetriNet.ReducesTo.refl _ _

/-- Reductions compose. -/
theorem trans {Place₁ Place₂ : Type u} {Transition₁ Transition₂ : Type v} [DecidableEq Place₁]
    [DecidableEq Place₂] {N₁ : ExecPetriNet Place₁ Transition₁} {M₁ : Multiset Place₁}
    {N₂ : ExecPetriNet Place₂ Transition₂} {M₂ : Multiset Place₂}
    (h₁ : N.ReducesTo M₀ N₁ M₁) (h₂ : N₁.ReducesTo M₁ N₂ M₂) : N.ReducesTo M₀ N₂ M₂ :=
  PetriNet.ReducesTo.trans h₁ h₂

/-- Rename the places and the transitions along bijections. -/
theorem reindex {Place' : Type u} {Transition' : Type v} [DecidableEq Place']
    (e : Place ≃ Place') (f : Transition ≃ Transition') :
    N.ReducesTo M₀ (N.rename e f) (M₀.map e) := by
  unfold ReducesTo
  rw [toPetriNet_rename, toFinsupp_map]
  exact PetriNet.ReducesTo.reindex e f

/-- Rename the places along a bijection. -/
theorem reindexPlaces {Place' : Type u} [DecidableEq Place'] (e : Place ≃ Place') :
    N.ReducesTo M₀ (N.renamePlaces e) (M₀.map e) := by
  unfold ReducesTo
  rw [toPetriNet_renamePlaces, toFinsupp_map]
  exact PetriNet.ReducesTo.reindex e (Equiv.refl _)

/-- Rename the transitions along a bijection. -/
theorem reindexTransitions {Transition' : Type v} (f : Transition ≃ Transition') :
    N.ReducesTo M₀ (N.renameTransitions f) M₀ := by
  unfold ReducesTo
  rw [toPetriNet_renameTransitions]
  have := PetriNet.ReducesTo.reindex (N := N.toPetriNet) (M₀ := Multiset.toFinsupp M₀)
    (Equiv.refl Place) f
  rwa [Marking.rename_refl] at this

/-- A reduction of the weighted net that deletes a place is a reduction of the executable
net. -/
theorem of_removePlace {p : Place}
    (h : PetriNet.ReducesTo N.toPetriNet (Multiset.toFinsupp M₀) (N.toPetriNet.removePlace p)
      (Marking.drop p (Multiset.toFinsupp M₀))) :
    N.ReducesTo M₀ (N.removePlace p) (dropMarking p M₀) := by
  unfold ReducesTo
  rwa [toPetriNet_removePlace, toFinsupp_dropMarking]

/-- A reduction of the weighted net that fuses a drained place is a reduction of the executable
net. -/
theorem of_fuseDelete {t : Transition} {p : Place}
    (h : PetriNet.ReducesTo N.toPetriNet (Multiset.toFinsupp M₀)
      (N.toPetriNet.fuseDelete t p)
      (Marking.drop p (N.toPetriNet.collapse t p (Multiset.toFinsupp M₀)))) :
    N.ReducesTo M₀ (N.fuseDelete t p) (dropMarking p (N.collapseMarking t p M₀)) := by
  unfold ReducesTo
  rwa [toPetriNet_fuseDelete, toFinsupp_dropMarking, toFinsupp_collapseMarking]

/-- Delete a self-loop place: it is initially marked enough for every transition, and every
transition consumes as many tokens from it as it produces. -/
theorem selfLoopPlace (p : Place) (hmark : ∀ t, (N.pre t).count p ≤ M₀.count p)
    (hloop : ∀ t, (N.post t).count p = (N.pre t).count p) :
    N.ReducesTo M₀ (N.removePlace p) (dropMarking p M₀) :=
  of_removePlace (PetriNet.ReducesTo.selfLoopPlace p
    (fun t => by simpa [Multiset.toFinsupp_apply] using hmark t) fun t => by simpa using hloop t)

/-- Delete a place that is parallel to a place `q` with no more tokens initially. -/
theorem parallelPlace {p q : Place} (h : N.toPetriNet.ParallelPlaces p q)
    (h₀ : M₀.count q ≤ M₀.count p) : N.ReducesTo M₀ (N.removePlace p) (dropMarking p M₀) :=
  of_removePlace (PetriNet.ReducesTo.parallelPlace h (by simpa [Multiset.toFinsupp_apply] using h₀))

/-- Delete an isolated place. -/
theorem isolatedPlace {p : Place} (h : N.toPetriNet.IsIsolated p) :
    N.ReducesTo M₀ (N.removePlace p) (dropMarking p M₀) :=
  of_removePlace (PetriNet.ReducesTo.isolatedPlace h)

/-- Delete one of two parallel transitions. -/
theorem removeParallelTransition {t₁ t₂ : Transition} (h : N.toPetriNet.ParallelTransitions t₁ t₂) :
    N.ReducesTo M₀ (N.removeTransition t₂) M₀ := by
  unfold ReducesTo
  rw [toPetriNet_removeTransition]
  exact PetriNet.ReducesTo.removeTransition h

/-- Delete a self-loop transition, given the side conditions of `PetriNet.ReducesTo`: it is never
the only enabled transition at a reachable marking, and it is live whenever the reduced net is.
These are not decidable in general; see `selfLoopTransition_of_twin`. -/
theorem selfLoopTransition {t : Transition} (h : N.toPetriNet.IsSelfLoopTransition t)
    (hd : ∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → M [t⟩[N.toPetriNet] →
      ∃ u, u ≠ t ∧ M [u⟩[N.toPetriNet])
    (hl : (N.toPetriNet.removeTransition t).Live (Multiset.toFinsupp M₀) →
      N.toPetriNet.LiveAt (Multiset.toFinsupp M₀) t) :
    N.ReducesTo M₀ (N.removeTransition t) M₀ := by
  unfold ReducesTo
  rw [toPetriNet_removeTransition]
  exact PetriNet.ReducesTo.selfLoopTransition h hd hl

/-- Deleting a self-loop transition preserves and reflects boundedness, with no further side
condition. -/
theorem bounded_removeTransition_of_pre_eq_post {t : Transition} (h : N.pre t = N.post t) :
    (N.removeTransition t).toPetriNet.Bounded (Multiset.toFinsupp M₀) ↔
      N.toPetriNet.Bounded (Multiset.toFinsupp M₀) := by
  rw [toPetriNet_removeTransition]
  exact (isSelfLoopTransition_iff.2 h).bounded_removeTransition_iff

/-- Delete a self-loop transition `t` that has a twin `u` with the same preset. The condition is
decidable, and implies the side conditions of `selfLoopTransition`. -/
theorem selfLoopTransition_of_twin {t u : Transition} (h : N.pre t = N.post t) (hu : u ≠ t)
    (hpre : N.pre u = N.pre t) : N.ReducesTo M₀ (N.removeTransition t) M₀ := by
  unfold ReducesTo
  rw [toPetriNet_removeTransition]
  exact PetriNet.ReducesTo.selfLoopTransition_of_twin (isSelfLoopTransition_iff.2 h) hu
    (congrArg Multiset.toFinsupp hpre)

/-- Fuse a place with the transition that drains it, and delete the place. The transition has to
produce a token somewhere, and some transition has to produce into the place. -/
theorem fuseDrain {t : Transition} {p : Place} (h : N.toPetriNet.IsDrain t p)
    (hpost : N.post t ≠ 0) (hprod : ∃ t₁, p ∈ N.post t₁) :
    N.ReducesTo M₀ (N.fuseDelete t p) (dropMarking p (N.collapseMarking t p M₀)) := by
  obtain ⟨q, hq⟩ := Multiset.exists_mem_of_ne_zero hpost
  obtain ⟨t₁, ht₁⟩ := hprod
  exact of_fuseDelete (PetriNet.ReducesTo.fuseDrain h
    ⟨q, by rw [post_apply]; exact Multiset.count_pos.2 hq⟩
    ⟨t₁, by rw [post_apply]; exact Multiset.count_pos.2 ht₁⟩)

/-- Fusion of series transitions `t₁ → p → t₂` (Murata's FST), deleting `p`. The transition `t₂`
has to produce a token somewhere. -/
theorem fuseSeries {t₁ t₂ : Transition} {p : Place} (h : N.toPetriNet.IsSeries t₁ t₂ p)
    (hpost : N.post t₂ ≠ 0) :
    N.ReducesTo M₀ (N.fuseDelete t₂ p) (dropMarking p (N.collapseMarking t₂ p M₀)) :=
  fuseDrain h.toIsDrain hpost ⟨t₁, Multiset.count_pos.1 (by simpa using h.post_pos)⟩

/-- Fusion of series places `p₁ → t → p₂` (Murata's FSP), deleting `p₁`. Some transition has to
produce into `p₁`. -/
theorem fuseSeriesPlace {t : Transition} {p₁ p₂ : Place} (h : N.toPetriNet.IsSeriesPlace t p₁ p₂)
    (hprod : ∃ t₁, p₁ ∈ N.post t₁) :
    N.ReducesTo M₀ (N.fuseDelete t p₁) (dropMarking p₁ (N.collapseMarking t p₁ M₀)) := by
  refine fuseDrain h.toIsDrain ?_ hprod
  rw [(isSeriesPlace_iff.1 h).2.2.1]
  exact Multiset.singleton_ne_zero _

end Rules

section Transfer

variable {Place Place' : Type u} {Transition Transition' : Type v} [DecidableEq Place]
  [DecidableEq Place'] {N : ExecPetriNet Place Transition} {M₀ : Multiset Place}
  {N' : ExecPetriNet Place' Transition'} {M₀' : Multiset Place'}

/-- The reduced net is bounded iff the original net is. -/
theorem bounded_iff (h : N.ReducesTo M₀ N' M₀') :
    N'.toPetriNet.Bounded (Multiset.toFinsupp M₀') ↔ N.toPetriNet.Bounded (Multiset.toFinsupp M₀) :=
  PetriNet.ReducesTo.bounded_iff h

/-- A `k`-bounded net reduces to a `k`-bounded net. -/
theorem kBounded (h : N.ReducesTo M₀ N' M₀') {k : ℕ}
    (hk : N.toPetriNet.KBounded (Multiset.toFinsupp M₀) k) :
    N'.toPetriNet.KBounded (Multiset.toFinsupp M₀') k :=
  PetriNet.ReducesTo.kBounded h hk

/-- The reduced net reaches a dead marking iff the original net does. -/
theorem exists_dead_iff (h : N.ReducesTo M₀ N' M₀') :
    (∃ K, (Multiset.toFinsupp M₀') ⇝[N'.toPetriNet] K ∧ N'.toPetriNet.Dead K) ↔
      ∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M :=
  PetriNet.ReducesTo.exists_dead_iff h

/-- The reduced net is live iff the original net is. -/
theorem live_iff (h : N.ReducesTo M₀ N' M₀') :
    N'.toPetriNet.Live (Multiset.toFinsupp M₀') ↔ N.toPetriNet.Live (Multiset.toFinsupp M₀) :=
  PetriNet.ReducesTo.live_iff h

end Transfer

end ReducesTo

namespace ReducesWF

variable {Place Place' : Type u} {Transition Transition' : Type v} [DecidableEq Place]
  [DecidableEq Place'] {N : ExecPetriNet Place Transition} {i o : Place}

/-- The empty reduction. -/
theorem refl (N : ExecPetriNet Place Transition) (i o : Place) : N.ReducesWF i o N i o :=
  PetriNet.ReducesWF.refl _ _ _

/-- Reductions compose. -/
theorem trans {Place₁ Place₂ : Type u} {Transition₁ Transition₂ : Type v} [DecidableEq Place₁]
    [DecidableEq Place₂] {N₁ : ExecPetriNet Place₁ Transition₁} {i₁ o₁ : Place₁}
    {N₂ : ExecPetriNet Place₂ Transition₂} {i₂ o₂ : Place₂}
    (h₁ : N.ReducesWF i o N₁ i₁ o₁) (h₂ : N₁.ReducesWF i₁ o₁ N₂ i₂ o₂) :
    N.ReducesWF i o N₂ i₂ o₂ :=
  PetriNet.ReducesWF.trans h₁ h₂

/-- Rename the places and the transitions along bijections, and the source and the sink with
them. -/
theorem reindex {Place' : Type u} {Transition' : Type v} [DecidableEq Place']
    (e : Place ≃ Place') (f : Transition ≃ Transition') :
    N.ReducesWF i o (N.rename e f) (e i) (e o) := by
  unfold ReducesWF
  rw [toPetriNet_rename]
  exact PetriNet.ReducesWF.reindex e f

/-- Rename the transitions along a bijection; the source and the sink are places. -/
theorem reindexTransitions {Transition' : Type v} (f : Transition ≃ Transition') :
    N.ReducesWF i o (N.renameTransitions f) i o := by
  unfold ReducesWF
  rw [toPetriNet_renameTransitions]
  exact PetriNet.ReducesWF.reindex (Equiv.refl Place) f

/-- Delete one of two parallel transitions on a workflow net. -/
theorem removeParallelTransition {t₁ t₂ : Transition}
    (h : N.toPetriNet.ParallelTransitions t₁ t₂) :
    N.ReducesWF i o (N.removeTransition t₂) i o := by
  unfold ReducesWF
  rw [toPetriNet_removeTransition]
  exact PetriNet.ReducesWF.removeTransition h

/-- Fuse a place with the transition that drains it on a workflow net, and delete the place. The
source and the sink must not be the deleted place. -/
theorem fuseDrain {t : Transition} {p : Place} (h : N.toPetriNet.IsDrain t p) (hi : i ≠ p)
    (ho : o ≠ p) : N.ReducesWF i o (N.fuseDelete t p) ⟨i, hi⟩ ⟨o, ho⟩ := by
  unfold ReducesWF
  rw [toPetriNet_fuseDelete]
  exact PetriNet.ReducesWF.fuseDrain h hi ho

/-- Fusion of series transitions `t₁ → p → t₂` (Murata's FST) on a workflow net. -/
theorem fuseSeries {t₁ t₂ : Transition} {p : Place} (h : N.toPetriNet.IsSeries t₁ t₂ p)
    (hi : i ≠ p) (ho : o ≠ p) : N.ReducesWF i o (N.fuseDelete t₂ p) ⟨i, hi⟩ ⟨o, ho⟩ :=
  fuseDrain h.toIsDrain hi ho

/-- Fusion of series places `p₁ → t → p₂` (Murata's FSP) on a workflow net. -/
theorem fuseSeriesPlace {t : Transition} {p₁ p₂ : Place}
    (h : N.toPetriNet.IsSeriesPlace t p₁ p₂) (hi : i ≠ p₁) (ho : o ≠ p₁) :
    N.ReducesWF i o (N.fuseDelete t p₁) ⟨i, hi⟩ ⟨o, ho⟩ :=
  fuseDrain h.toIsDrain hi ho

/-- Along a certificate, the reduced net is a workflow net, and it is sound iff the original net
is. -/
theorem isWFNet_and_sound {N' : ExecPetriNet Place' Transition'} {i' o' : Place'}
    (h : N.ReducesWF i o N' i' o') (hN : N.toPetriNet.IsWFNet i o) :
    N'.toPetriNet.IsWFNet i' o' ∧ (N'.toPetriNet.Sound i' o' ↔ N.toPetriNet.Sound i o) :=
  PetriNet.ReducesWF.isWFNet_and_sound h hN

end ReducesWF

end ExecPetriNet

end Cslib
