/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Deleting a place

Deleting a place `p` from a net, and restricting markings accordingly. Every firing of the original
net is a firing of the reduced net; the converse holds when `p` has enough tokens. Both operations
are computable: restricting a marking drops the tokens in `p` (`Multiset.filterMap`).

## Main definitions

- `PetriNet.Marking.drop`: a marking restricted to the places other than `p`.
- `PetriNet.removePlace`: the net with a place deleted.
- `PetriNet.IsIsolated`: no transition consumes from or produces into the place; decidable for
  finitely many transitions.

## Main statements

- `PetriNet.Fires.drop`, `PetriNet.mTr_drop`, `PetriNet.Reachable.drop`: firings, firing sequences
  and reachability of `N` give those of the net with `p` deleted.
- `PetriNet.enabled_iff_drop`: a transition is enabled exactly when it is enabled in the reduced
  net and `p` has enough tokens; `PetriNet.Fires.of_drop` lifts the firing.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open LTS

variable {Place : Type*} {Transition : Type*}

/-- A place is *isolated* if no transition consumes from it or produces into it. -/
def IsIsolated (N : PetriNet Place Transition) (p : Place) : Prop :=
  ∀ t, p ∉ •[N] t ∧ p ∉ t •[N]

instance [DecidableEq Place] [Fintype Transition] (N : PetriNet Place Transition) (p : Place) :
    Decidable (N.IsIsolated p) :=
  inferInstanceAs (Decidable (∀ _, _))

variable [DecidableEq Place]

/-! ### Restricting markings -/

/-- A marking restricted to the places other than `p`: the tokens in `p` are dropped. -/
def Marking.drop (p : Place) (M : Marking Place) : Marking {q // q ≠ p} :=
  M.filterMap fun q => if h : q = p then none else some ⟨q, h⟩

namespace Marking

variable (p : Place)

@[simp] theorem drop_zero : (0 : Marking Place).drop p = 0 := rfl

theorem drop_cons_self (M : Marking Place) : Marking.drop p (p ::ₘ M) = M.drop p :=
  Multiset.filterMap_cons_none _ _ (by simp)

theorem drop_cons_of_ne {q : Place} (h : q ≠ p) (M : Marking Place) :
    Marking.drop p (q ::ₘ M) = ⟨q, h⟩ ::ₘ M.drop p :=
  Multiset.filterMap_cons_some _ _ _ (by simp [h])

/-- The tokens of a restricted marking in a place other than `p`. -/
@[simp] theorem count_drop (M : Marking Place) (q : {q // q ≠ p}) :
    (M.drop p).count q = M.count q.1 := by
  induction M using Multiset.induction with
  | empty => simp
  | cons a M ih =>
    by_cases h : a = p
    · subst h
      rw [drop_cons_self, ih, Multiset.count_cons_of_ne q.2]
    · rw [drop_cons_of_ne p h, Multiset.count_cons, ih, Multiset.count_cons]
      simp [Subtype.ext_iff]

@[simp] theorem mem_drop {M : Marking Place} {q : {q // q ≠ p}} : q ∈ M.drop p ↔ q.1 ∈ M := by
  simp only [← Multiset.count_pos, count_drop]

/-- Restriction commutes with the sum of markings. -/
@[simp] theorem drop_add (M K : Marking Place) : (M + K).drop p = M.drop p + K.drop p :=
  Multiset.filterMap_add _ _ _

/-- Restriction commutes with truncated subtraction of markings. -/
@[simp] theorem drop_sub (M K : Marking Place) : (M - K).drop p = M.drop p - K.drop p := by
  ext q
  simp

@[simp] theorem drop_nsmul (n : ℕ) (M : Marking Place) : (n • M).drop p = n • M.drop p := by
  ext q
  simp

/-- Restriction of a single token placed at `q`: it is dropped if `q = p`. -/
theorem drop_singleton (q : Place) :
    Marking.drop p {q} = if h : q = p then 0 else {⟨q, h⟩} := by
  split_ifs with h
  · subst h
    exact drop_cons_self q 0
  · exact drop_cons_of_ne p h 0

variable {p}

/-- Restriction is monotone. -/
theorem drop_le_drop {M K : Marking Place} (h : M ≤ K) : M.drop p ≤ K.drop p :=
  Multiset.le_iff_count.2 fun q => by simpa using Multiset.le_iff_count.1 h q.1

/-- A marking is determined by its restriction and the tokens in the deleted place. -/
theorem eq_of_drop_eq {M K : Marking Place} (hM : p ∉ M) (hK : p ∉ K)
    (h : M.drop p = K.drop p) : M = K := by
  ext q
  by_cases hq : q = p
  · subst hq
    rw [Multiset.count_eq_zero.2 hM, Multiset.count_eq_zero.2 hK]
  · simpa using congrArg (Multiset.count ⟨q, hq⟩) h

end Marking

/-! ### Deleting a place -/

/-- The net with the place `p` deleted. -/
def removePlace (N : PetriNet Place Transition) (p : Place) :
    PetriNet {q // q ≠ p} Transition where
  pre t := Marking.drop p (•[N] t)
  post t := Marking.drop p (t •[N])

@[simp] theorem removePlace_pre (N : PetriNet Place Transition) (p : Place) (t : Transition) :
    (N.removePlace p).pre t = Marking.drop p (•[N] t) := rfl

@[simp] theorem removePlace_post (N : PetriNet Place Transition) (p : Place) (t : Transition) :
    (N.removePlace p).post t = Marking.drop p (t •[N]) := rfl

variable {N : PetriNet Place Transition} {p : Place}

/-- A transition is enabled exactly when it is enabled in the net with `p` deleted and `p` holds
enough tokens for it. -/
theorem enabled_iff_drop {M : Marking Place} {t : Transition} :
    M [t⟩[N] ↔ (M.drop p) [t⟩[N.removePlace p] ∧ (•[N] t).count p ≤ M.count p := by
  refine ⟨fun h => ⟨Marking.drop_le_drop h, Multiset.count_le_of_le p h⟩, fun ⟨h, hp⟩ => ?_⟩
  refine Multiset.le_iff_count.2 fun q => ?_
  by_cases hq : q = p
  · exact hq ▸ hp
  · simpa using Multiset.le_iff_count.1 h ⟨q, hq⟩

/-- Firing in `N` gives firing in the net with `p` deleted. -/
theorem Fires.drop {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    (M.drop p) [t⟩[N.removePlace p] (M'.drop p) := by
  obtain ⟨R, rfl, rfl⟩ := h
  exact ⟨R.drop p, by simp, by simp⟩

/-- A firing in the net with `p` deleted lifts to `N` if `p` has enough tokens for `t`. -/
theorem Fires.of_drop {M : Marking Place} {t : Transition} {K : Marking {q // q ≠ p}}
    (hp : (•[N] t).count p ≤ M.count p) (h : (M.drop p) [t⟩[N.removePlace p] K) :
    ∃ M', M [t⟩[N] M' ∧ M'.drop p = K := by
  obtain ⟨hen, rfl⟩ := fires_iff.1 h
  exact ⟨N.fire M t, fires_iff.2 ⟨enabled_iff_drop.2 ⟨hen, hp⟩, rfl⟩, by simp [fire]⟩

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

/-! ### Isolated places -/

/-- The tokens in an isolated place never change. -/
theorem IsIsolated.count_eq_of_reachable (h : N.IsIsolated p) {M₀ M : Marking Place}
    (hr : M₀ ⇝[N] M) : M.count p = M₀.count p :=
  hr.invariant (P := fun K => K.count p = M₀.count p) (fun {K t K'} htr hP => by
    obtain ⟨R, rfl, rfl⟩ := htr
    simp only [Multiset.count_add, Multiset.count_eq_zero.2 (h t).1,
      Multiset.count_eq_zero.2 (h t).2] at hP ⊢
    omega) rfl

/-- A transition is enabled in the net without an isolated place exactly when it is enabled in the
net. -/
theorem IsIsolated.enabled_iff (h : N.IsIsolated p) {M : Marking Place} {t : Transition} :
    (M.drop p) [t⟩[N.removePlace p] ↔ M [t⟩[N] := by
  rw [enabled_iff_drop (p := p), Multiset.count_eq_zero.2 (h t).1]
  simp

end PetriNet

end Cslib
