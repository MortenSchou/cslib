/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Data.Set.Card
public import Mathlib.Data.Set.Finite.Basic

/-! # Ranking a finite set by successive exits

If every nonempty subset `Y` of a finite set `Z` has an element with a witness `u` that relates only
to elements outside `Q ∪ Y`, then the elements of `Z` can be ranked so that the witness of each
element relates, within `Z`, only to elements of smaller rank. This is the combinatorial core of the
necessity half of Commoner's theorem for Petri nets.

## Main statements

- `Cslib.exists_rank`: the ranking and the witnesses.
-/

@[expose] public section

namespace Cslib

/-- A ranking of the set `Z`, built one element at a time. Every nonempty `Y ⊆ Z` has `u`, `y ∈ Y`
with `pre u y` such that `post u` holds only outside `Q ∪ Y`. Then every `z ∈ Z` has `e z` with
`pre (e z) z` such that `post (e z)` holds, within `Z`, only on elements of smaller rank, and
nowhere in `Q`. -/
theorem exists_rank {α β : Type*} [Finite α] [Nonempty β]
    (Z Q : Set α) (pre post : β → α → Prop)
    (H : ∀ Y ⊆ Z, Y.Nonempty →
      ∃ u, ∃ y ∈ Y, pre u y ∧ ∀ s, post u s → s ∉ Q ∧ s ∉ Y) :
    ∃ (f : α → ℕ) (e : α → β), Set.InjOn f Z ∧
      ∀ z ∈ Z, pre (e z) z ∧ ∀ s, post (e z) s → s ∉ Q ∧ (s ∈ Z → f s < f z) := by
  classical
  have key : ∀ n, n ≤ Z.ncard → ∃ D : Finset α, ↑D ⊆ Z ∧ D.card = n ∧
      ∃ (f : α → ℕ) (e : α → β), (∀ z ∈ D, f z < n) ∧ Set.InjOn f ↑D ∧
        ∀ z ∈ D, pre (e z) z ∧ ∀ s, post (e z) s → s ∉ Q ∧ (s ∈ Z → s ∈ D ∧ f s < f z) := by
    intro n
    induction n with
    | zero =>
      intro _
      exact ⟨∅, by simp, by simp, fun _ => 0, fun _ => Classical.arbitrary β,
        by simp, by simp, by simp⟩
    | succ n ih =>
      intro hn
      obtain ⟨D, hDZ, hcard, f, e, hf, hinj, hprop⟩ := ih (by omega)
      have hY : (Z \ ↑D).Nonempty := by
        by_contra hne
        rw [Set.not_nonempty_iff_eq_empty, Set.sdiff_eq_empty] at hne
        have := Set.ncard_le_ncard hne (Finset.finite_toSet D)
        rw [Set.ncard_coe_finset] at this
        omega
      obtain ⟨u, y, hyY, hpre, hpost⟩ := H (Z \ ↑D) Set.sdiff_subset hY
      have hyD : y ∉ D := fun h => hyY.2 h
      have hyZ : y ∈ Z := hyY.1
      refine ⟨insert y D, ?_, ?_, Function.update f y D.card, Function.update e y u, ?_, ?_, ?_⟩
      · intro z hz
        rcases Finset.mem_insert.1 (Finset.mem_coe.1 hz) with rfl | hz
        · exact hyZ
        · exact hDZ hz
      · rw [Finset.card_insert_of_notMem hyD, hcard]
      · intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzD
        · simp [hcard]
        · have hzy : z ≠ y := by rintro rfl; exact hyD hzD
          rw [Function.update_of_ne hzy]
          have := hf z hzD
          omega
      · intro a ha b hb hab
        simp only [Finset.coe_insert, Set.mem_insert_iff, Finset.mem_coe] at ha hb
        rcases ha with rfl | ha <;> rcases hb with rfl | hb
        · rfl
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hyD hb)] at hab
          have := hf b hb
          omega
        · rw [Function.update_self, Function.update_of_ne (by rintro rfl; exact hyD ha)] at hab
          have := hf a ha
          omega
        · rw [Function.update_of_ne (by rintro rfl; exact hyD ha),
            Function.update_of_ne (by rintro rfl; exact hyD hb)] at hab
          exact hinj ha hb hab
      · intro z hz
        rcases Finset.mem_insert.1 hz with rfl | hzD
        · refine ⟨by simpa using hpre, fun s hs => ?_⟩
          obtain ⟨hsQ, hsY⟩ := hpost s (by simpa using hs)
          refine ⟨hsQ, fun hsZ => ?_⟩
          have hsD : s ∈ D := by
            by_contra h; exact hsY ⟨hsZ, fun h' => h (Finset.mem_coe.1 h')⟩
          have hsy : s ≠ z := by rintro rfl; exact hyD hsD
          refine ⟨Finset.mem_insert_of_mem hsD, ?_⟩
          simp only [Function.update_of_ne hsy, Function.update_self]
          have := hf s hsD
          omega
        · have hzy : z ≠ y := by rintro rfl; exact hyD hzD
          obtain ⟨hpz, hpp⟩ := hprop z hzD
          refine ⟨by simpa [Function.update_of_ne hzy] using hpz, fun s hs => ?_⟩
          rw [Function.update_of_ne hzy] at hs
          obtain ⟨hsQ, hsrest⟩ := hpp s hs
          refine ⟨hsQ, fun hsZ => ?_⟩
          obtain ⟨hsD, hlt⟩ := hsrest hsZ
          have hsy : s ≠ y := by rintro rfl; exact hyD hsD
          refine ⟨Finset.mem_insert_of_mem hsD, ?_⟩
          simpa [Function.update_of_ne hzy, Function.update_of_ne hsy] using hlt
  obtain ⟨D, hDZ, hcard, f, e, -, hinj, hprop⟩ := key Z.ncard le_rfl
  have hDeq : (↑D : Set α) = Z :=
    Set.eq_of_subset_of_ncard_le hDZ (by rw [Set.ncard_coe_finset, hcard]) (Set.toFinite Z)
  subst hDeq
  refine ⟨f, e, hinj, fun z hz => ?_⟩
  obtain ⟨hp, hpp⟩ := hprop z (Finset.mem_coe.1 hz)
  exact ⟨hp, fun s hs => ⟨(hpp s hs).1, fun hsZ => (hpp s hs).2 hsZ |>.2⟩⟩

end Cslib
