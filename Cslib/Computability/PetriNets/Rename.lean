/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.SoundnessNotions
public import Mathlib.Data.Finsupp.Basic

/-! # Renaming the places and transitions of a net

An isomorphism of nets is a pair of bijections of the places and of the transitions. The net
`N.rename e f` is the net `N` with its places renamed along `e` and its transitions along `f`, and
`Marking.rename e` renames a marking. Renaming leaves the marking graph unchanged up to the
renaming of its states and labels, so it preserves every behavioural property: reachability,
boundedness, deadlocks, liveness, the structure of a workflow net and soundness.

Renaming is the means to keep long chains of reductions manageable. Deleting a place or a
transition passes to a subtype, and `n` deletions give `n` nested subtypes; renaming the result to
`Fin n` after each step keeps the types flat (see
`Cslib.Computability.PetriNets.ExecutableReductionSearch`).

## Main definitions

- `PetriNet.rename`: the net with renamed places and transitions.
- `PetriNet.Marking.rename`: the marking with renamed places, an additive equivalence.

## Main statements

- `PetriNet.reachable_rename_iff`: reachability is preserved and reflected.
- `PetriNet.kBounded_rename_iff`, `PetriNet.bounded_rename_iff`, `PetriNet.dead_rename_iff`,
  `PetriNet.liveAt_rename_iff`, `PetriNet.live_rename_iff`.
- `PetriNet.isWFNet_rename_iff`, `PetriNet.sound_rename_iff`: workflow nets and soundness, with the
  source and the sink renamed.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS
open scoped PetriNet

universe u₁ u₂ v₁ v₂

variable {Place : Type u₁} {Place' : Type u₂} {Transition : Type v₁} {Transition' : Type v₂}

/-- A marking with its places renamed along a bijection. -/
def Marking.rename (e : Place ≃ Place') : Marking Place ≃+ Marking Place' :=
  Finsupp.domCongr e

@[simp] theorem Marking.rename_apply (e : Place ≃ Place') (M : Marking Place) (q : Place') :
    Marking.rename e M q = M (e.symm q) := rfl

theorem Marking.rename_single (e : Place ≃ Place') (p : Place) (n : ℕ) :
    Marking.rename e (Finsupp.single p n) = Finsupp.single (e p) n :=
  Finsupp.equivMapDomain_single ..

@[simp] theorem Marking.rename_symm_rename (e : Place ≃ Place') (M : Marking Place) :
    Marking.rename e.symm (Marking.rename e M) = M := by
  ext p; simp

@[simp] theorem Marking.rename_rename_symm (e : Place ≃ Place') (M : Marking Place') :
    Marking.rename e (Marking.rename e.symm M) = M := by
  ext p; simp

@[simp] theorem Marking.rename_refl (M : Marking Place) : Marking.rename (Equiv.refl Place) M = M :=
  Finsupp.equivMapDomain_refl M

theorem Marking.rename_le_iff (e : Place ≃ Place') {M K : Marking Place} :
    Marking.rename e M ≤ Marking.rename e K ↔ M ≤ K := by
  simp only [Finsupp.le_def, Marking.rename_apply]
  exact ⟨fun h p => by simpa using h (e p), fun h q => h _⟩

theorem Marking.rename_surjective (e : Place ≃ Place') :
    Function.Surjective (Marking.rename e) := (Marking.rename e).surjective

/-- The net with the places renamed along `e` and the transitions along `f`. -/
def rename (N : PetriNet Place Transition) (e : Place ≃ Place') (f : Transition ≃ Transition') :
    PetriNet Place' Transition' where
  pre t := Marking.rename e (N.pre (f.symm t))
  post t := Marking.rename e (N.post (f.symm t))

variable {N : PetriNet Place Transition} (e : Place ≃ Place') (f : Transition ≃ Transition')

@[simp] theorem rename_pre (t : Transition) :
    (N.rename e f).pre (f t) = Marking.rename e (N.pre t) := by simp [rename]

@[simp] theorem rename_post (t : Transition) :
    (N.rename e f).post (f t) = Marking.rename e (N.post t) := by simp [rename]

/-- Renaming back gives the original net. -/
@[simp] theorem rename_symm_rename : (N.rename e f).rename e.symm f.symm = N := by
  cases N with
  | mk pre post =>
    simp only [rename, Equiv.symm_symm, Marking.rename_symm_rename, Equiv.symm_apply_apply]

/-- Firing is preserved and reflected by renaming. -/
theorem fires_rename_iff {M M' : Marking Place} {t : Transition} :
    (N.rename e f).Fires (Marking.rename e M) (f t) (Marking.rename e M') ↔ M [t⟩[N] M' := by
  unfold Fires
  simp only [rename_pre, rename_post]
  constructor
  · rintro ⟨R, h₁, h₂⟩
    refine ⟨Marking.rename e.symm R, ?_, ?_⟩
    · apply (Marking.rename e).injective
      rw [h₁, map_add]; simp
    · apply (Marking.rename e).injective
      rw [h₂, map_add]; simp
  · rintro ⟨R, rfl, rfl⟩
    exact ⟨Marking.rename e R, by rw [map_add], by rw [map_add]⟩

/-- Enabling is preserved and reflected by renaming. -/
theorem enabled_rename_iff {M : Marking Place} {t : Transition} :
    (N.rename e f).Enabled (Marking.rename e M) (f t) ↔ M [t⟩[N] := by
  rw [enabled_iff_exists_fires, enabled_iff_exists_fires]
  constructor
  · rintro ⟨M', h⟩
    obtain ⟨M'', rfl⟩ := Marking.rename_surjective e M'
    exact ⟨M'', (fires_rename_iff e f).1 h⟩
  · rintro ⟨M', h⟩
    exact ⟨Marking.rename e M', (fires_rename_iff e f).2 h⟩

/-- Firing sequences are carried along by renaming. -/
theorem mTr_rename {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') :
    (N.rename e f).lts.MTr (Marking.rename e M) (ts.map f) (Marking.rename e M') := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL ((fires_rename_iff e f).2 htr) ih

/-- Reachability is carried along by renaming. -/
theorem Reachable.rename {M M' : Marking Place} (h : M ⇝[N] M') :
    Marking.rename e M ⇝[N.rename e f] Marking.rename e M' :=
  let ⟨ts, h⟩ := h
  ⟨ts.map f, mTr_rename e f h⟩

/-- Reachability is preserved and reflected by renaming. -/
theorem reachable_rename_iff {M M' : Marking Place} :
    Marking.rename e M ⇝[N.rename e f] Marking.rename e M' ↔ M ⇝[N] M' := by
  refine ⟨fun h => ?_, Reachable.rename e f⟩
  have := Reachable.rename (N := N.rename e f) e.symm f.symm h
  simpa using this

/-- Boundedness bounds are preserved and reflected by renaming. -/
theorem kBounded_rename_iff {M₀ : Marking Place} {k : ℕ} :
    (N.rename e f).KBounded (Marking.rename e M₀) k ↔ N.KBounded M₀ k := by
  constructor
  · intro h M hM p
    have := h (Marking.rename e M) ((reachable_rename_iff e f).2 hM) (e p)
    simpa using this
  · intro h M' hM' q
    obtain ⟨M, rfl⟩ := Marking.rename_surjective e M'
    simpa using h M ((reachable_rename_iff e f).1 hM') (e.symm q)

theorem bounded_rename_iff {M₀ : Marking Place} :
    (N.rename e f).Bounded (Marking.rename e M₀) ↔ N.Bounded M₀ := by
  simp only [Bounded, kBounded_rename_iff]

/-- Dead markings correspond under renaming. -/
theorem dead_rename_iff {M : Marking Place} :
    (N.rename e f).Dead (Marking.rename e M) ↔ N.Dead M := by
  simp only [dead_iff]
  exact (f.forall_congr fun t => by rw [enabled_rename_iff e f]).symm

/-- A dead marking is reachable after renaming iff one is reachable before. -/
theorem exists_dead_rename_iff {M₀ : Marking Place} :
    (∃ K, Marking.rename e M₀ ⇝[N.rename e f] K ∧ (N.rename e f).Dead K) ↔
      ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  constructor
  · rintro ⟨K, hK, hd⟩
    obtain ⟨M, rfl⟩ := Marking.rename_surjective e K
    exact ⟨M, (reachable_rename_iff e f).1 hK, (dead_rename_iff e f).1 hd⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨Marking.rename e M, (reachable_rename_iff e f).2 hM, (dead_rename_iff e f).2 hd⟩

theorem liveAt_rename_iff {M₀ : Marking Place} {t : Transition} :
    (N.rename e f).LiveAt (Marking.rename e M₀) (f t) ↔ N.LiveAt M₀ t := by
  constructor
  · intro h M hM
    obtain ⟨K, hK, hen⟩ := h (Marking.rename e M) ((reachable_rename_iff e f).2 hM)
    obtain ⟨M', rfl⟩ := Marking.rename_surjective e K
    exact ⟨M', (reachable_rename_iff e f).1 hK, (enabled_rename_iff e f).1 hen⟩
  · intro h M' hM'
    obtain ⟨M, rfl⟩ := Marking.rename_surjective e M'
    obtain ⟨K, hK, hen⟩ := h M ((reachable_rename_iff e f).1 hM')
    exact ⟨Marking.rename e K, (reachable_rename_iff e f).2 hK, (enabled_rename_iff e f).2 hen⟩

theorem live_rename_iff {M₀ : Marking Place} :
    (N.rename e f).Live (Marking.rename e M₀) ↔ N.Live M₀ :=
  (f.forall_congr fun _ => (liveAt_rename_iff e f).symm).symm

/-! ### Workflow nets -/

theorem Marking.rename_token (e : Place ≃ Place') (p : Place) :
    Marking.rename e (token p) = token (e p) :=
  Marking.rename_single e p 1

theorem arc_rename_iff (a b : Place ⊕ Transition) :
    (N.rename e f).Arc (Sum.map e f a) (Sum.map e f b) ↔ N.Arc a b := by
  rcases a with p | t <;> rcases b with q | u <;> simp [Arc, rename]

/-- Renaming a workflow net gives a workflow net. -/
theorem IsWFNet.rename {i o : Place} (h : N.IsWFNet i o) :
    (N.rename e f).IsWFNet (e i) (e o) where
  no_input_source t' := by
    obtain ⟨t, rfl⟩ := f.surjective t'
    simpa using h.no_input_source t
  no_output_sink t' := by
    obtain ⟨t, rfl⟩ := f.surjective t'
    simpa using h.no_output_sink t
  reach_from_source n' := by
    obtain ⟨n, rfl⟩ := (Equiv.sumCongr e f).surjective n'
    exact (Relation.ReflTransGen.lift (Sum.map e f)
      (fun a b hab => (arc_rename_iff e f a b).2 hab)) _ _ (h.reach_from_source n)
  reach_to_sink n' := by
    obtain ⟨n, rfl⟩ := (Equiv.sumCongr e f).surjective n'
    exact (Relation.ReflTransGen.lift (Sum.map e f)
      (fun a b hab => (arc_rename_iff e f a b).2 hab)) _ _ (h.reach_to_sink n)

theorem isWFNet_rename_iff {i o : Place} : (N.rename e f).IsWFNet (e i) (e o) ↔ N.IsWFNet i o := by
  refine ⟨fun h => ?_, IsWFNet.rename e f⟩
  simpa using IsWFNet.rename (N := N.rename e f) e.symm f.symm h

/-- Soundness is preserved by renaming, with the source and the sink renamed. -/
theorem Sound.rename {i o : Place} (h : N.Sound i o) : (N.rename e f).Sound (e i) (e o) := by
  have hi := Marking.rename_token e i
  have ho := Marking.rename_token e o
  refine ⟨fun M' hM' => ?_, fun M' hM' hle => ?_, fun t' => ?_⟩
  · obtain ⟨M, rfl⟩ := Marking.rename_surjective e M'
    rw [← hi] at hM'
    rw [← ho]
    exact (reachable_rename_iff e f).2 (h.completion M ((reachable_rename_iff e f).1 hM'))
  · obtain ⟨M, rfl⟩ := Marking.rename_surjective e M'
    rw [← hi] at hM'
    rw [← ho] at hle ⊢
    rw [h.proper M ((reachable_rename_iff e f).1 hM') ((Marking.rename_le_iff e).1 hle)]
  · obtain ⟨t, rfl⟩ := f.surjective t'
    obtain ⟨M, hM, hen⟩ := h.noDead t
    rw [← hi]
    exact ⟨Marking.rename e M, (reachable_rename_iff e f).2 hM, (enabled_rename_iff e f).2 hen⟩

/-- Soundness is preserved and reflected by renaming, with the source and the sink renamed. -/
theorem sound_rename_iff {i o : Place} : (N.rename e f).Sound (e i) (e o) ↔ N.Sound i o :=
  ⟨fun h => by simpa using Sound.rename (N := N.rename e f) e.symm f.symm h, Sound.rename e f⟩

end PetriNet

end Cslib
