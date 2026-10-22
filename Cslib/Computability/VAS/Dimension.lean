/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.AsympDefinable
public import Mathlib.Algebra.Group.Pointwise.Set.Scalar
public import Mathlib.LinearAlgebra.FiniteDimensional.Defs
public import Mathlib.LinearAlgebra.Span.Defs
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.Data.Nat.Cast.WithTop

/-!
# Dimension of sets of integer vectors

The dimension of a set `X ⊆ ℤ^κ` is the least `m` such that `X` is covered by finitely many affine
translates `b + V` of `ℚ`-subspaces `V ⊆ ℚ^κ` of rank at most `m` (and `⊥` for the empty set).

## Main definitions

* `Cslib.VAS.DimLE`: `X` is covered by finitely many affine spaces of rank `≤ d`.
* `Cslib.VAS.dim`: the dimension, valued in `WithBot ℕ`.

## Main results

* `Cslib.VAS.dim_empty`, `Cslib.VAS.dim_vadd`, `Cslib.VAS.dim_union`, `Cslib.VAS.dim_mono`: the
  dimension of `∅` is `⊥`, it is translation invariant, `dim` of a union is the maximum, and `dim`
  is monotone.
* `Cslib.VAS.periodic_subset_vectorSpace`: a periodic set covered by finitely many affine spaces is
  contained in one of the underlying vector spaces (Leroux, Lemma 7.3).
* `Cslib.VAS.dim_periodic`: the dimension of a periodic set is the rank of the vector space it
  generates (Leroux, Lemma 7.4).

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

open scoped Pointwise

namespace Cslib.VAS

variable {κ : Type*}

/-- `DimLE X d`: `X ⊆ ℤ^κ` is covered by finitely many affine translates `b + V` of
`ℚ`-subspaces of rank at most `d`. -/
def DimLE (X : Set (κ → ℤ)) (d : WithBot ℕ) : Prop :=
  ∃ S : Set ((κ → ℤ) × Submodule ℚ (κ → ℚ)), S.Finite ∧
    (∀ s ∈ S, (Module.finrank ℚ s.2 : WithBot ℕ) ≤ d) ∧ ∀ x ∈ X, ∃ s ∈ S, ratVec (x - s.1) ∈ s.2

/-- The dimension of `X`: the least `d` with `DimLE X d`, so `⊥` (`= -1`) for the empty set. It is
only meaningful for finite `κ`. -/
noncomputable def dim (X : Set (κ → ℤ)) : WithBot ℕ := sInf {d | DimLE X d}

namespace DimLE

variable {X Y : Set (κ → ℤ)} {d e : WithBot ℕ}

theorem empty (d : WithBot ℕ) : DimLE (∅ : Set (κ → ℤ)) d :=
  ⟨∅, Set.finite_empty, by simp, by simp⟩

theorem mono_dim (h : DimLE X d) (hde : d ≤ e) : DimLE X e := by
  obtain ⟨S, hS, hr, hc⟩ := h
  exact ⟨S, hS, fun s hs => (hr s hs).trans hde, hc⟩

theorem mono_set (h : DimLE Y d) (hXY : X ⊆ Y) : DimLE X d := by
  obtain ⟨S, hS, hr, hc⟩ := h
  exact ⟨S, hS, hr, fun x hx => hc x (hXY hx)⟩

theorem union (hX : DimLE X d) (hY : DimLE Y d) : DimLE (X ∪ Y) d := by
  obtain ⟨S, hS, hr, hc⟩ := hX
  obtain ⟨T, hT, hr', hc'⟩ := hY
  refine ⟨S ∪ T, hS.union hT, fun s hs => hs.elim (hr s) (hr' s), ?_⟩
  rintro x (hx | hx)
  · obtain ⟨s, hs, h⟩ := hc x hx
    exact ⟨s, Or.inl hs, h⟩
  · obtain ⟨s, hs, h⟩ := hc' x hx
    exact ⟨s, Or.inr hs, h⟩

theorem vadd (h : DimLE X d) (v : κ → ℤ) : DimLE (v +ᵥ X) d := by
  obtain ⟨S, hS, hr, hc⟩ := h
  refine ⟨(fun s => (v + s.1, s.2)) '' S, hS.image _, ?_, ?_⟩
  · rintro _ ⟨s, hs, rfl⟩
    exact hr s hs
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := Set.mem_vadd_set.1 hy
    obtain ⟨s, hs, h⟩ := hc x hx
    refine ⟨(v + s.1, s.2), ⟨s, hs, rfl⟩, ?_⟩
    simpa only [vadd_eq_add, add_sub_add_left_eq_sub] using h

/-- A set is covered by affine spaces of rank at most `⊥` only if it is empty. -/
theorem eq_empty_of_bot (h : DimLE X ⊥) : X = ∅ := by
  obtain ⟨S, -, hr, hc⟩ := h
  refine Set.eq_empty_of_forall_notMem fun x hx => ?_
  obtain ⟨s, hs, -⟩ := hc x hx
  simpa using hr s hs

end DimLE

section Fin

variable [Finite κ] {X Y : Set (κ → ℤ)} {d : WithBot ℕ}

/-- Every set is covered by the whole space, which has finite rank. -/
theorem DimLE.exists (X : Set (κ → ℤ)) : ∃ d, DimLE X d := by
  have := Fintype.ofFinite κ
  refine ⟨Fintype.card κ, {(0, ⊤)}, Set.finite_singleton _, fun s hs => ?_,
    fun x _ => ⟨(0, ⊤), rfl, Submodule.mem_top⟩⟩
  rw [Set.mem_singleton_iff.1 hs]
  simp

/-- `dim X ≤ d` is the same as `DimLE X d`. -/
theorem dim_le_iff : dim X ≤ d ↔ DimLE X d :=
  ⟨fun h => (csInf_mem (s := {d | DimLE X d}) (DimLE.exists X)).mono_dim h,
    fun h => csInf_le (OrderBot.bddBelow _) h⟩

theorem dim_eq_bot_iff : dim X = ⊥ ↔ X = ∅ := by
  rw [← le_bot_iff, dim_le_iff]
  exact ⟨DimLE.eq_empty_of_bot, fun h => h ▸ DimLE.empty _⟩

theorem dim_empty : dim (∅ : Set (κ → ℤ)) = ⊥ := dim_eq_bot_iff.2 rfl

/-- If `X` is non-empty then its dimension is a natural number. -/
theorem exists_dim_eq (h : X.Nonempty) : ∃ m : ℕ, dim X = m := by
  induction hd : dim X using WithBot.recBotCoe with
  | bot => exact absurd (dim_eq_bot_iff.1 hd) h.ne_empty
  | coe m => exact ⟨m, rfl⟩

/-- Monotonicity of the dimension. -/
theorem dim_mono (h : X ⊆ Y) : dim X ≤ dim Y :=
  dim_le_iff.2 ((dim_le_iff.1 le_rfl).mono_set h)

/-- The dimension of a union is the maximum of the dimensions. -/
theorem dim_union (X Y : Set (κ → ℤ)) : dim (X ∪ Y) = max (dim X) (dim Y) :=
  le_antisymm
    (dim_le_iff.2 ((dim_le_iff.1 (le_max_left _ _)).union (dim_le_iff.1 (le_max_right _ _))))
    (max_le (dim_mono Set.subset_union_left) (dim_mono Set.subset_union_right))

/-- A finite union of sets of dimension at most `d` has dimension at most `d`. -/
theorem dim_biUnion_le {α : Type*} {s : Set α} (hs : s.Finite) {t : α → Set (κ → ℤ)}
    (h : ∀ i ∈ s, dim (t i) ≤ d) : dim (⋃ i ∈ s, t i) ≤ d := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simp [dim_empty]
  | insert ha hs ih =>
    rw [Set.biUnion_insert, dim_union, max_le_iff]
    exact ⟨h _ (Set.mem_insert _ _), ih fun i hi => h i (Set.mem_insert_of_mem _ hi)⟩

/-- A finite union of sets of dimension below `d` has dimension below `d`, provided `⊥ < d`. -/
theorem dim_biUnion_lt {α : Type*} {s : Set α} (hs : s.Finite) {t : α → Set (κ → ℤ)}
    (hd : ⊥ < d) (h : ∀ i ∈ s, dim (t i) < d) : dim (⋃ i ∈ s, t i) < d := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa [dim_empty] using hd
  | insert ha hs ih =>
    rw [Set.biUnion_insert, dim_union, max_lt_iff]
    exact ⟨h _ (Set.mem_insert _ _), ih fun i hi => h i (Set.mem_insert_of_mem _ hi)⟩

/-- The dimension is invariant under translation. -/
theorem dim_vadd (v : κ → ℤ) (X : Set (κ → ℤ)) : dim (v +ᵥ X) = dim X := by
  have key (v : κ → ℤ) (X : Set (κ → ℤ)) : dim (v +ᵥ X) ≤ dim X :=
    dim_le_iff.2 ((dim_le_iff.1 le_rfl).vadd v)
  refine le_antisymm (key v X) ?_
  simpa only [vadd_vadd, neg_add_cancel, zero_vadd] using key (-v) (v +ᵥ X)

omit [Finite κ] in
/-- A periodic subset of a `ℚ`-vector space contained in a finite union of subspaces is contained
in one of them. -/
theorem periodic_subset_iUnion {E : Type*} [AddCommGroup E] [Module ℚ E] {P : Set E}
    (hP : IsPeriodic P) {ι : Type*} (V : ι → Submodule ℚ E) (s : Finset ι)
    (h : ∀ p ∈ P, ∃ j ∈ s, p ∈ V j) : ∃ j ∈ s, ∀ p ∈ P, p ∈ V j := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using h 0 hP.1
  | insert a s ha ih =>
    by_cases hPa : ∀ p ∈ P, p ∈ V a
    · exact ⟨a, Finset.mem_insert_self _ _, hPa⟩
    push Not at hPa
    obtain ⟨p₀, hp₀, hp₀a⟩ := hPa
    obtain ⟨j, hj, hj'⟩ := ih fun q hq => by
      obtain ⟨j, hj, hqj⟩ := h q hq
      by_cases hqa : q ∈ V a
      · -- the points `p₀ + n • q` of `P` avoid `V a`, so two of them lie in the same `V j`
        have hpick : ∀ n : ℕ, ∃ j : s, p₀ + n • q ∈ V j := fun n => by
          obtain ⟨j, hj, hmem⟩ := h (p₀ + n • q) (hP.2 _ hp₀ _ (hP.nsmul_mem hq n))
          rcases Finset.mem_insert.1 hj with rfl | hj
          · exact absurd (by simpa using (V j).sub_mem hmem ((V j).nsmul_mem hqa n)) hp₀a
          · exact ⟨⟨j, hj⟩, hmem⟩
        choose f hf using hpick
        obtain ⟨n, m, hnm, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
        have hm' : p₀ + m • q ∈ V (f n) := by rw [hfe]; exact hf m
        have hd : ((n : ℚ) - m) • q ∈ V (f n) := by
          have := (V (f n)).sub_mem (hf n) hm'
          rwa [add_sub_add_left_eq_sub, ← Nat.cast_smul_eq_nsmul ℚ n, ← Nat.cast_smul_eq_nsmul ℚ m,
            ← sub_smul] at this
        have hne : ((n : ℚ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hnm)
        exact ⟨(f n).1, (f n).2, ((V (f n)).smul_mem_iff hne).1 hd⟩
      · rcases Finset.mem_insert.1 hj with rfl | hj
        · exact absurd hqj hqa
        · exact ⟨j, hj, hqj⟩
    exact ⟨j, Finset.mem_insert_of_mem hj, hj'⟩

omit [Finite κ] in
/-- **Lemma 7.3** (Leroux): a periodic set covered by finitely many affine spaces `b_j + V_j` is
contained in one `V_j`, and then `b_j ∈ V_j`. (Stated for an arbitrary finite index type.) -/
theorem periodic_subset_vectorSpace {P : Set (κ → ℤ)} (hP : IsPeriodic P) {ι : Type*} [Finite ι]
    (b : ι → (κ → ℤ)) (V : ι → Submodule ℚ (κ → ℚ))
    (h : ∀ p ∈ P, ∃ j, ratVec (p - b j) ∈ V j) :
    ∃ j, (∀ p ∈ P, ratVec p ∈ V j) ∧ ratVec (b j) ∈ V j := by
  classical
  -- every point of `P` lies in some `V j` with `b j ∈ V j`
  have step : ∀ p ∈ P, ∃ j, ratVec p ∈ V j ∧ ratVec (b j) ∈ V j := by
    intro p hp
    choose f hf using fun n : ℕ => h (n • p) (hP.nsmul_mem hp n)
    obtain ⟨n, m, hnm, hfe⟩ := Finite.exists_ne_map_eq_of_infinite f
    have hm' : ratVec (m • p - b (f n)) ∈ V (f n) := by rw [hfe]; exact hf m
    have hd : ((n : ℚ) - m) • ratVec p ∈ V (f n) := by
      have := (V (f n)).sub_mem (hf n) hm'
      rwa [← ratVec_sub, sub_sub_sub_cancel_right, ratVec_sub, ratVec_nsmul, ratVec_nsmul,
        ← sub_smul] at this
    have hne : ((n : ℚ) - m) ≠ 0 := sub_ne_zero.2 (by exact_mod_cast hnm)
    have hpn : ratVec p ∈ V (f n) := ((V (f n)).smul_mem_iff hne).1 hd
    refine ⟨f n, hpn, ?_⟩
    have h1 := (V (f n)).sub_mem ((V (f n)).smul_mem (n : ℚ) hpn) (hf n)
    rwa [← ratVec_nsmul, ← ratVec_sub, sub_sub_cancel] at h1
  -- the good indices
  let J := {j // ratVec (b j) ∈ V j}
  have : Finite J := inferInstance
  let _ : Fintype J := Fintype.ofFinite J
  have hP' : IsPeriodic (ratVec '' P) :=
    isPeriodic_coe (hP.toAddSubmonoid.map (AddMonoidHom.compLeft (Int.castAddHom ℚ) κ))
  obtain ⟨j, -, hj⟩ := periodic_subset_iUnion hP' (fun j : J => V j.1) Finset.univ (by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨j, hj, hj'⟩ := step p hp
    exact ⟨⟨j, hj'⟩, Finset.mem_univ _, hj⟩)
  exact ⟨j.1, fun p hp => hj _ ⟨p, hp, rfl⟩, j.2⟩

/-- **Lemma 7.4** (Leroux): the dimension of a periodic set is the rank of the vector space it
generates. -/
theorem dim_periodic {P : Set (κ → ℤ)} (hP : IsPeriodic P) :
    dim P = ((Module.finrank ℚ (Submodule.span ℚ (ratVec '' P)) : ℕ) : WithBot ℕ) := by
  refine le_antisymm (dim_le_iff.2 ⟨{(0, Submodule.span ℚ (ratVec '' P))},
    Set.finite_singleton _, by simp, fun x hx => ⟨_, rfl, ?_⟩⟩) ?_
  · simpa using Submodule.subset_span (Set.mem_image_of_mem ratVec hx)
  · obtain ⟨S, hS, hr, hc⟩ := dim_le_iff.1 (le_refl (dim P))
    have := hS.to_subtype
    obtain ⟨j, hj, -⟩ := periodic_subset_vectorSpace hP (fun j : S => j.1.1) (fun j => j.1.2)
      (fun p hp => by
        obtain ⟨s, hs, h⟩ := hc p hp
        exact ⟨⟨s, hs⟩, h⟩)
    have hle : Submodule.span ℚ (ratVec '' P) ≤ j.1.2 :=
      Submodule.span_le.2 (by rintro _ ⟨p, hp, rfl⟩; exact hj p hp)
    exact (WithBot.coe_le_coe.2 (Submodule.finrank_mono hle)).trans (hr _ j.2)

end Fin

end Cslib.VAS
