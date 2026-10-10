/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Data.Fintype.Powerset
public import Mathlib.Order.FixedPoints

/-! # Fixpoints of monotone operators on finite sets

Iterating a monotone operator on the finite subsets of a finite type reaches a fixpoint after
`Fintype.card α` steps, from `∅` or from `univ`. The iterates compute the least and greatest
fixpoints of a monotone operator on sets that is computed by the operator on finite sets.

## Main statements

- `Cslib.iterate_empty_stable`, `Cslib.iterate_univ_stable`: the iteration is stable after
  `Fintype.card α` steps.
- `Cslib.lfp_eq_iterate`, `Cslib.gfp_eq_iterate`: the iterates compute the least and greatest
  fixpoints.
-/

@[expose] public section

namespace Cslib

variable {α : Type*} [Fintype α]

/-- Iterating a monotone operator on finite sets from `∅` reaches a fixpoint after `card α`
steps. -/
theorem iterate_empty_stable {F : Finset α → Finset α} (hF : Monotone F) :
    F (F^[Fintype.card α] ∅) = F^[Fintype.card α] ∅ := by
  classical
  set a : ℕ → Finset α := fun n => F^[n] ∅ with ha
  have hsucc : ∀ n, a (n + 1) = F (a n) := fun n => Function.iterate_succ_apply' F n ∅
  have hle : ∀ n, a n ⊆ a (n + 1) := fun n => by
    induction n with
    | zero => exact Finset.empty_subset _
    | succ n ih =>
      have := hF ih
      rwa [← hsucc n, ← hsucc (n + 1)] at this
  have key : ∀ n, (∃ k ≤ n, a k = a (k + 1)) ∨ n ≤ (a n).card := fun n => by
    induction n with
    | zero => exact Or.inr (Nat.zero_le _)
    | succ n ih =>
      rcases ih with ⟨k, hk, h⟩ | h
      · exact Or.inl ⟨k, by omega, h⟩
      · by_cases heq : a n = a (n + 1)
        · exact Or.inl ⟨n, Nat.le_succ n, heq⟩
        · exact Or.inr (Nat.succ_le_of_lt (lt_of_le_of_lt h
            (Finset.card_lt_card (Finset.ssubset_iff_subset_ne.2 ⟨hle n, heq⟩))))
  change F (a (Fintype.card α)) = a (Fintype.card α)
  rw [← hsucc]
  rcases key (Fintype.card α) with ⟨k, hk, h⟩ | h
  · have hk' : ∀ j, a (k + j) = a k := fun j => by
      induction j with
      | zero => rfl
      | succ j ih => rw [← add_assoc, hsucc, ih, ← hsucc, ← h]
    have h1 := hk' (Fintype.card α - k)
    have h2 := hk' (Fintype.card α - k + 1)
    rw [show k + (Fintype.card α - k) = Fintype.card α by omega] at h1
    rw [show k + (Fintype.card α - k + 1) = Fintype.card α + 1 by omega] at h2
    rw [h1, h2]
  · have : a (Fintype.card α) = Finset.univ :=
      Finset.eq_univ_of_card _ (le_antisymm (Finset.card_le_univ _) h)
    exact le_antisymm (by rw [this]; exact Finset.subset_univ _) (hle _)

/-- Iterating a monotone operator on finite sets from `univ` reaches a fixpoint after `card α`
steps. -/
theorem iterate_univ_stable {F : Finset α → Finset α} (hF : Monotone F) :
    F (F^[Fintype.card α] Finset.univ) = F^[Fintype.card α] Finset.univ := by
  classical
  set G : Finset α → Finset α := fun X => (F Xᶜ)ᶜ with hG
  have hGm : Monotone G := fun X Y h =>
    Finset.compl_subset_compl.2 (hF (Finset.compl_subset_compl.2 h))
  have hiter : ∀ n, G^[n] ∅ = (F^[n] Finset.univ)ᶜ := fun n => by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih, hG]
      simp
  have := iterate_empty_stable hGm
  rw [hiter, hG] at this
  simpa using this

/-- The least fixpoint of a set operator computed by a monotone operator on finite sets. -/
theorem lfp_eq_iterate {F : Finset α → Finset α} (hF : Monotone F) (f : Set α →o Set α)
    (h : ∀ X, ((F X : Finset α) : Set α) = f X) :
    OrderHom.lfp f = (F^[Fintype.card α] ∅ : Finset α) := by
  classical
  apply le_antisymm
  · refine OrderHom.lfp_le _ ?_
    rw [← h, iterate_empty_stable hF]
  · have : ∀ n, ((F^[n] ∅ : Finset α) : Set α) ≤ OrderHom.lfp f := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', h]
        calc f _ ≤ f (OrderHom.lfp f) := f.monotone ih
          _ = OrderHom.lfp f := f.map_lfp
    exact this _

/-- The greatest fixpoint of a set operator computed by a monotone operator on finite sets. -/
theorem gfp_eq_iterate {F : Finset α → Finset α} (hF : Monotone F) (f : Set α →o Set α)
    (h : ∀ X, ((F X : Finset α) : Set α) = f X) :
    OrderHom.gfp f = (F^[Fintype.card α] Finset.univ : Finset α) := by
  classical
  apply le_antisymm
  · have : ∀ n, OrderHom.gfp f ≤ ((F^[n] Finset.univ : Finset α) : Set α) := fun n => by
      induction n with
      | zero => simp
      | succ n ih =>
        rw [Function.iterate_succ_apply', h]
        calc OrderHom.gfp f = f (OrderHom.gfp f) := f.map_gfp.symm
          _ ≤ f _ := f.monotone ih
    exact this _
  · refine OrderHom.le_gfp _ ?_
    rw [← h, iterate_univ_stable hF]

end Cslib
