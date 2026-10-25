/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.SoundnessNotions

/-! # Renaming the places and transitions of a net

An isomorphism of nets is a pair of bijections of the places and of the transitions. The net
`N.rename e f` is the net `N` with its places renamed along `e` and its transitions along `f`; a
marking `M` is renamed to `M.map e`. Renaming leaves the marking graph unchanged up to the renaming
of its states and labels, so it preserves every behavioural property: reachability, boundedness,
deadlocks, liveness, the structure of a workflow net and soundness.

Renaming is the means to keep long chains of reductions manageable. Deleting a place or a
transition passes to a subtype, and `n` deletions give `n` nested subtypes; renaming the result to
`Fin n` after each step keeps the types flat (see
`Cslib.Computability.PetriNets.Decision.ReductionSearch`).

## Main definitions

- `PetriNet.rename`: the net with renamed places and transitions (computable).

## Main statements

- `PetriNet.enabled_map_iff`, `PetriNet.fires_map_iff`, `PetriNet.mTr_map`,
  `PetriNet.reachable_map_iff`: a renaming of the places and transitions that respects the arcs
  preserves and reflects the behaviour.
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

/-! ### Renaming places and transitions -/

section Renaming

variable {Place Place' Transition Transition' : Type*} {N : PetriNet Place Transition}
  {N' : PetriNet Place' Transition'} (σ : Place ≃ Place') {τ : Transition → Transition'}

/-- Renaming the places of a marking along the inverse of a bijection, and then along the
bijection, gives back the marking. -/
theorem map_symm_map (M : Marking Place') : (M.map σ.symm).map σ = M := by
  simp [Multiset.map_map]

/-- Renaming the places of a marking along a bijection, and then along its inverse, gives back the
marking. -/
theorem symm_map_map (M : Marking Place) : (M.map σ).map σ.symm = M := by
  simp [Multiset.map_map]

/-- A renaming of the places and transitions that respects the arcs preserves and reflects
enabling. -/
theorem enabled_map_iff (hpre : ∀ t, •[N'] (τ t) = (•[N] t).map σ) {M : Marking Place}
    {t : Transition} : (M.map σ) [τ t⟩[N'] ↔ M [t⟩[N] := by
  rw [Enabled, Enabled, hpre, Multiset.map_le_map_iff σ.injective]

/-- A renaming of the places and transitions that respects the arcs preserves and reflects
firing. -/
theorem fires_map_iff (hpre : ∀ t, •[N'] (τ t) = (•[N] t).map σ)
    (hpost : ∀ t, (τ t) •[N'] = (t •[N]).map σ) {M M' : Marking Place} {t : Transition} :
    (M.map σ) [τ t⟩[N'] (M'.map σ) ↔ M [t⟩[N] M' := by
  constructor
  · rintro ⟨R, h₁, h₂⟩
    refine ⟨R.map σ.symm, Multiset.map_injective σ.injective ?_,
      Multiset.map_injective σ.injective ?_⟩
    · rw [Multiset.map_add, map_symm_map, ← hpre]
      exact h₁
    · rw [Multiset.map_add, map_symm_map, ← hpost]
      exact h₂
  · rintro ⟨R, rfl, rfl⟩
    exact ⟨R.map σ, by rw [Multiset.map_add, hpre], by rw [Multiset.map_add, hpost]⟩

/-- A renaming of the places and transitions that respects the arcs maps firing sequences to
firing sequences. -/
theorem mTr_map (hpre : ∀ t, •[N'] (τ t) = (•[N] t).map σ)
    (hpost : ∀ t, (τ t) •[N'] = (t •[N]).map σ) {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : N'.lts.MTr (M.map σ) (ts.map τ) (M'.map σ) := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL ((fires_map_iff σ hpre hpost).2 htr) ih

/-- A renaming of the places and transitions that respects the arcs, and is onto the
transitions, preserves and reflects reachability. -/
theorem reachable_map_iff (hτ : Function.Surjective τ) (hpre : ∀ t, •[N'] (τ t) = (•[N] t).map σ)
    (hpost : ∀ t, (τ t) •[N'] = (t •[N]).map σ) {M M' : Marking Place} :
    (M.map σ) ⇝[N'] (M'.map σ) ↔ M ⇝[N] M' := by
  constructor
  · intro h
    obtain ⟨K, hK, hr⟩ := h.invariant (P := fun K => ∃ K₀, K = K₀.map σ ∧ M ⇝[N] K₀)
      (fun {K t' K'} hf ⟨K₀, hK, hr⟩ => by
        obtain ⟨t, rfl⟩ := hτ t'
        subst hK
        rw [← map_symm_map σ K'] at hf
        exact ⟨K'.map σ.symm, (map_symm_map σ K').symm,
          hr.trans ((fires_map_iff σ hpre hpost).1 hf).reachable⟩) ⟨M, rfl, .refl _ _⟩
    rwa [Multiset.map_injective σ.injective hK]
  · rintro ⟨ts, h⟩
    exact ⟨_, mTr_map σ hpre hpost h⟩

end Renaming

/-! ### The renamed net -/

variable {Place Place' Transition Transition' : Type*}

/-- The net with the places renamed along `e` and the transitions along `f`. -/
def rename (N : PetriNet Place Transition) (e : Place ≃ Place') (f : Transition ≃ Transition') :
    PetriNet Place' Transition' where
  pre t := (•[N] (f.symm t)).map e
  post t := ((f.symm t) •[N]).map e

variable {N : PetriNet Place Transition} (e : Place ≃ Place') (f : Transition ≃ Transition')

@[simp] theorem rename_pre (t : Transition) : •[N.rename e f] (f t) = (•[N] t).map e := by
  simp [rename]

@[simp] theorem rename_post (t : Transition) : (f t) •[N.rename e f] = (t •[N]).map e := by
  simp [rename]

/-- Renaming back gives the original net. -/
@[simp] theorem rename_symm_rename : (N.rename e f).rename e.symm f.symm = N := by
  cases N
  simp only [rename, Equiv.symm_symm, Equiv.symm_apply_apply, symm_map_map]

/-- Enabling is preserved and reflected by renaming. -/
theorem enabled_rename_iff {M : Marking Place} {t : Transition} :
    (M.map e) [f t⟩[N.rename e f] ↔ M [t⟩[N] :=
  enabled_map_iff e (rename_pre e f)

/-- Firing is preserved and reflected by renaming. -/
theorem fires_rename_iff {M M' : Marking Place} {t : Transition} :
    (M.map e) [f t⟩[N.rename e f] (M'.map e) ↔ M [t⟩[N] M' :=
  fires_map_iff e (rename_pre e f) (rename_post e f)

/-- Reachability is preserved and reflected by renaming. -/
theorem reachable_rename_iff {M M' : Marking Place} :
    (M.map e) ⇝[N.rename e f] (M'.map e) ↔ M ⇝[N] M' :=
  reachable_map_iff e f.surjective (rename_pre e f) (rename_post e f)

/-- The markings reachable after renaming are the renamed reachable markings. -/
theorem exists_reachable_rename_iff {M : Marking Place} {K : Marking Place'} :
    (M.map e) ⇝[N.rename e f] K ↔ ∃ M', M ⇝[N] M' ∧ M'.map e = K := by
  refine ⟨fun h => ⟨K.map e.symm, ?_, map_symm_map e K⟩, fun ⟨M', hM', hK⟩ => ?_⟩
  · rw [← reachable_rename_iff e f, map_symm_map]
    exact h
  · rw [← hK]
    exact (reachable_rename_iff e f).2 hM'

/-- Boundedness bounds are preserved and reflected by renaming. -/
theorem kBounded_rename_iff {M₀ : Marking Place} {k : ℕ} :
    (N.rename e f).KBounded (M₀.map e) k ↔ N.KBounded M₀ k := by
  simp only [KBounded, exists_reachable_rename_iff]
  constructor
  · intro h M hM p hle
    refine h _ ⟨M, hM, rfl⟩ (e p) ?_
    rw [← Multiset.map_replicate]
    exact Multiset.map_le_map hle
  · rintro h _ ⟨M, hM, rfl⟩ q hle
    refine h M hM (e.symm q) ((Multiset.map_le_map_iff e.injective).1 ?_)
    rwa [Multiset.map_replicate, Equiv.apply_symm_apply]

theorem bounded_rename_iff {M₀ : Marking Place} :
    (N.rename e f).Bounded (M₀.map e) ↔ N.Bounded M₀ := by
  simp only [Bounded, kBounded_rename_iff]

/-- Dead markings correspond under renaming. -/
theorem dead_rename_iff {M : Marking Place} :
    (N.rename e f).Dead (M.map e) ↔ N.Dead M := by
  simp only [dead_iff]
  exact (f.forall_congr fun t => by rw [enabled_rename_iff e f]).symm

/-- A dead marking is reachable after renaming iff one is reachable before. -/
theorem exists_dead_rename_iff {M₀ : Marking Place} :
    (∃ K, M₀.map e ⇝[N.rename e f] K ∧ (N.rename e f).Dead K) ↔ ∃ M, M₀ ⇝[N] M ∧ N.Dead M := by
  simp only [exists_reachable_rename_iff]
  constructor
  · rintro ⟨_, ⟨M, hM, rfl⟩, hd⟩
    exact ⟨M, hM, (dead_rename_iff e f).1 hd⟩
  · rintro ⟨M, hM, hd⟩
    exact ⟨M.map e, ⟨M, hM, rfl⟩, (dead_rename_iff e f).2 hd⟩

theorem liveAt_rename_iff {M₀ : Marking Place} {t : Transition} :
    (N.rename e f).LiveAt (M₀.map e) (f t) ↔ N.LiveAt M₀ t := by
  constructor
  · intro h M hM
    obtain ⟨K, hK, hen⟩ := h (M.map e) ((reachable_rename_iff e f).2 hM)
    obtain ⟨M', hM', rfl⟩ := (exists_reachable_rename_iff e f).1 hK
    exact ⟨M', hM', (enabled_rename_iff e f).1 hen⟩
  · rintro h _ hM'
    obtain ⟨M, hM, rfl⟩ := (exists_reachable_rename_iff e f).1 hM'
    obtain ⟨K, hK, hen⟩ := h M hM
    exact ⟨K.map e, (reachable_rename_iff e f).2 hK, (enabled_rename_iff e f).2 hen⟩

theorem live_rename_iff {M₀ : Marking Place} :
    (N.rename e f).Live (M₀.map e) ↔ N.Live M₀ :=
  (f.forall_congr fun _ => (liveAt_rename_iff e f).symm).symm

/-! ### Workflow nets -/

theorem map_token (p : Place) : (token p).map e = token (e p) :=
  Multiset.map_singleton e p

theorem arc_rename_iff (a b : Place ⊕ Transition) :
    (N.rename e f).Arc (Sum.map e f a) (Sum.map e f b) ↔ N.Arc a b := by
  rcases a with p | t <;> rcases b with q | u <;>
    simp [Arc, rename, Multiset.mem_map_of_injective e.injective]

/-- Renaming a workflow net gives a workflow net. -/
theorem IsWFNet.rename {i o : Place} (h : N.IsWFNet i o) :
    (N.rename e f).IsWFNet (e i) (e o) where
  no_input_source t' := by
    obtain ⟨t, rfl⟩ := f.surjective t'
    simpa [rename, Multiset.mem_map_of_injective e.injective] using h.no_input_source t
  no_output_sink t' := by
    obtain ⟨t, rfl⟩ := f.surjective t'
    simpa [rename, Multiset.mem_map_of_injective e.injective] using h.no_output_sink t
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
  refine ⟨fun M' hM' => ?_, fun M' hM' hle => ?_, fun t' => ?_⟩
  · rw [← map_token] at hM' ⊢
    obtain ⟨M, hM, rfl⟩ := (exists_reachable_rename_iff e f).1 hM'
    exact (reachable_rename_iff e f).2 (h.completion M hM)
  · rw [← map_token] at hM' hle ⊢
    obtain ⟨M, hM, rfl⟩ := (exists_reachable_rename_iff e f).1 hM'
    rw [Multiset.map_le_map_iff e.injective] at hle
    rw [h.proper M hM hle]
  · rw [← map_token]
    obtain ⟨t, rfl⟩ := f.surjective t'
    obtain ⟨M, hM, hen⟩ := h.noDead t
    exact ⟨M.map e, (reachable_rename_iff e f).2 hM, (enabled_rename_iff e f).2 hen⟩

/-- Soundness is preserved and reflected by renaming, with the source and the sink renamed. -/
theorem sound_rename_iff {i o : Place} : (N.rename e f).Sound (e i) (e o) ↔ N.Sound i o :=
  ⟨fun h => by simpa using Sound.rename (N := N.rename e f) e.symm f.symm h, Sound.rename e f⟩

end PetriNet

end Cslib
