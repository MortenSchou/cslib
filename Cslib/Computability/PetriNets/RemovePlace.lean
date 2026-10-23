/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Deleting a place

Deleting a place `p` from a net, and restricting markings accordingly. Every firing of the original
net is a firing of the reduced net; the converse holds when `p` has enough tokens.

## Main definitions

- `PetriNet.removePlace`: the net with a place deleted.
- `PetriNet.Marking.drop`: a marking restricted to the places other than `p`.
- `PetriNet.IsIsolated`: no transition consumes from or produces into the place.

## Main statements

- `PetriNet.Fires.drop`, `PetriNet.mTr_drop`, `PetriNet.Reachable.drop`: firings, firing sequences
  and reachability of `N` give those of the net with `p` deleted.
- `PetriNet.Fires.of_drop`: a firing of the reduced net lifts if `p` has enough tokens.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS

variable {Place : Type*} {Transition : Type*}

/-- The net with the place `p` deleted. -/
noncomputable def removePlace (N : PetriNet Place Transition) (p : Place) :
    PetriNet {q // q ≠ p} Transition where
  pre t := (N.pre t).subtypeDomain (· ≠ p)
  post t := (N.post t).subtypeDomain (· ≠ p)

/-- A marking restricted to the places other than `p`; this is `Finsupp.subtypeDomain`. -/
noncomputable def Marking.drop (p : Place) (M : Marking Place) : Marking {q // q ≠ p} :=
  M.subtypeDomain (· ≠ p)

/-- Restricting a marking is `Finsupp.subtypeDomain`. -/
theorem Marking.drop_eq_subtypeDomain (p : Place) (M : Marking Place) :
    M.drop p = M.subtypeDomain (· ≠ p) := rfl

@[simp] theorem removePlace_pre (N : PetriNet Place Transition) (p : Place) (t : Transition) :
    (N.removePlace p).pre t = Marking.drop p (N.pre t) := rfl

@[simp] theorem removePlace_post (N : PetriNet Place Transition) (p : Place) (t : Transition) :
    (N.removePlace p).post t = Marking.drop p (N.post t) := rfl

/-- The value of a restricted marking at a place other than `p`. -/
@[simp] theorem Marking.drop_apply (p : Place) (M : Marking Place) (q : {q // q ≠ p}) :
    M.drop p q = M q := rfl

/-- Restriction commutes with the sum of markings. -/
@[simp] theorem Marking.drop_add (p : Place) (M K : Marking Place) :
    (M + K).drop p = M.drop p + K.drop p := Finsupp.subtypeDomain_add

@[simp] theorem Marking.drop_zero (p : Place) : (0 : Marking Place).drop p = 0 := rfl

/-- Restriction of a single token placed at `q`: it is dropped if `q = p`. -/
theorem Marking.drop_single [DecidableEq Place] (p q : Place) (n : ℕ) :
    Marking.drop p (Finsupp.single q n : Marking Place) =
      if h : q ≠ p then Finsupp.single ⟨q, h⟩ n else 0 := by
  ext ⟨r, hr⟩
  by_cases hq : q = p
  · subst hq
    simp [hr]
  · by_cases hrq : r = q
    · subst hrq
      simp [hq]
    · simp [hq, hrq, Subtype.ext_iff]

/-- Restriction commutes with truncated subtraction of markings. -/
@[simp] theorem Marking.drop_sub (p : Place) (M K : Marking Place) :
    (M - K).drop p = M.drop p - K.drop p := by
  ext q
  simp

variable {N : PetriNet Place Transition} {p : Place}

/-- A marking is determined by its restriction and the tokens in the deleted place. -/
theorem Marking.eq_of_drop_eq {M K : Marking Place} (hM : M p = 0) (hK : K p = 0)
    (h : M.drop p = K.drop p) : M = K := by
  ext q
  by_cases hq : q = p
  · subst hq
    rw [hM, hK]
  · exact congrArg (fun f => f ⟨q, hq⟩) h

/-- Firing in `N` gives firing in the net with `p` deleted. -/
theorem Fires.drop {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    (M.drop p) [t⟩[N.removePlace p] (M'.drop p) := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact ⟨R.drop p, by simp, by simp⟩

/-- A firing in the net with `p` deleted lifts to `N` if `p` has enough tokens for `t`. -/
theorem Fires.of_drop {M : Marking Place} {t : Transition} {K : Marking {q // q ≠ p}}
    (hp : (•[N] t) p ≤ M p) (h : (M.drop p) [t⟩[N.removePlace p] K) :
    ∃ M', M [t⟩[N] M' ∧ M'.drop p = K := by
  obtain ⟨R, hM, rfl⟩ := h
  have hle : •[N] t ≤ M := by
    refine Finsupp.le_def.2 fun q => ?_
    by_cases hq : q = p
    · subst hq
      exact hp
    · have := congrArg (fun f => f ⟨q, hq⟩) hM
      simp at this
      omega
  refine ⟨N.fire M t, fires_iff.2 ⟨hle, rfl⟩, ?_⟩
  ext ⟨q, hq⟩
  have := congrArg (fun f => f ⟨q, hq⟩) hM
  simp [fire] at this ⊢
  omega

/-- Firing sequences of `N` are firing sequences of the net with `p` deleted. -/
theorem mTr_drop {M M' : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M') :
    (N.removePlace p).lts.MTr (M.drop p) ts (M'.drop p) := by
  induction h with
  | refl => exact .refl
  | stepL htr _ ih => exact .stepL (Fires.drop htr) ih

/-- Reachability in `N` gives reachability in the net with `p` deleted. -/
theorem Reachable.drop {M M' : Marking Place} (h : M ⇝[N] M') :
    (M.drop p) ⇝[N.removePlace p] (M'.drop p) :=
  let ⟨ts, h⟩ := h
  ⟨ts, mTr_drop h⟩

/-- A place is *isolated* if no transition consumes from it or produces into it. -/
def IsIsolated (N : PetriNet Place Transition) (p : Place) : Prop :=
  ∀ t, (•[N] t) p = 0 ∧ (t •[N]) p = 0

/-- The tokens in an isolated place never change. -/
theorem IsIsolated.apply_eq_of_reachable (h : N.IsIsolated p) {M₀ M : Marking Place}
    (hr : M₀ ⇝[N] M) : M p = M₀ p :=
  hr.invariant (P := fun K => K p = M₀ p) (fun {K t K'} htr hP => by
    obtain ⟨R, rfl, rfl⟩ := htr
    have h1 := (h t).1
    have h2 := (h t).2
    simp only [Finsupp.add_apply] at hP ⊢
    omega) rfl

/-- A transition is enabled in the net without an isolated place exactly when it is enabled in the
net. -/
theorem IsIsolated.enabled_iff (h : N.IsIsolated p) {M : Marking Place} {t : Transition} :
    (N.removePlace p).Enabled (M.drop p) t ↔ N.Enabled M t := by
  constructor
  · intro he
    obtain ⟨K, hK⟩ := enabled_iff_exists_fires.1 he
    obtain ⟨M', hM', -⟩ := Fires.of_drop (by simp [(h t).1]) hK
    exact enabled_iff_exists_fires.2 ⟨M', hM'⟩
  · intro he
    obtain ⟨M', hM'⟩ := enabled_iff_exists_fires.1 he
    exact enabled_iff_exists_fires.2 ⟨_, Fires.drop hM'⟩

end PetriNet

end Cslib
