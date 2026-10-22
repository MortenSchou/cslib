/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.PostInter

/-! # Presburger separators and inductive invariants

A *separator* is a pair `(X, Y)` of Presburger sets of configurations with no run from `X` to `Y`.
Its *domain* is `ℕ^ι \ (X ∪ Y)`. From a separator with non-empty domain one builds a larger
separator whose domain has strictly smaller dimension (Leroux, Lemma 9.1). By induction on the
dimension, every separator is contained in a separator with empty domain, which yields a Presburger
inductive invariant (Theorem 9.2).

## Main results

* `VAS.separator_improve`: Lemma 9.1.
* `VAS.separator_complete`: every separator extends to a separator with empty domain.
* `VAS.exists_semilinear_invariant`: Theorem 9.2.
* `VAS.not_reach_iff`: `y` is not reachable from `x` iff a Presburger inductive invariant contains
  `x` and omits `y`.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

namespace VAS

variable {ι : Type*} {V : VAS ι}

/-- A linearization of the empty set is empty. -/
theorem IsLinearization.eq_empty [Fintype ι] {X S : Set (ι → ℤ)} (h : IsLinearization X S)
    (hX : X = ∅) : S = ∅ := by
  obtain ⟨F, -, hF, hXF, rfl⟩ := h
  have : F = ∅ := by
    refine Set.eq_empty_of_forall_notMem fun p hp => ?_
    have h0 : p.1 ∈ X := by
      rw [hXF]
      exact Set.mem_iUnion₂.2 ⟨p, hp, Set.mem_vadd_set.2 ⟨0, (hF p hp).1.1, add_zero _⟩⟩
    rw [hX] at h0
    exact h0
  simp [this]

/-- **Lemma 9.1** (Leroux): from a separator with non-empty domain one builds a larger separator
whose domain has strictly smaller dimension. -/
theorem separator_improve [Finite ι] {X₀ Y₀ : Set (VASConfig ι)} (h : V.Separator X₀ Y₀)
    (hD : (domain X₀ Y₀).Nonempty) :
    ∃ X Y : Set (VASConfig ι), V.Separator X Y ∧ X₀ ⊆ X ∧ Y₀ ⊆ Y ∧
      dim (toIntSet (domain X Y)) < dim (toIntSet (domain X₀ Y₀)) := by
  have := Fintype.ofFinite ι
  have hD₀ : IsSemilinearSet (domain X₀ Y₀) :=
    (h.semilinear_left.union h.semilinear_right).compl
  -- the forward part
  obtain ⟨S, hS⟩ := (almostSemilinear_post_inter (V := V) h.semilinear_left hD₀).1
  set Y := Y₀ ∪ (domain X₀ Y₀ \ {c | c.toInt ∈ S}) with hY
  have hYsl : IsSemilinearSet Y :=
    h.semilinear_right.union (hD₀.sdiff hS.isSemilinearSet_nat)
  have hsep₁ : V.Separator X₀ Y := by
    refine ⟨h.semilinear_left, hYsl, fun x hx y hy hxy => ?_⟩
    rcases hy with hy | ⟨hyD, hyS⟩
    · exact h.no_run x hx y hy hxy
    · exact hyS (hS.subset ⟨y, ⟨⟨x, hx, hxy⟩, hyD⟩, rfl⟩)
  -- the backward part
  obtain ⟨T, hT⟩ := (almostSemilinear_post_inter (V := V) hD₀ hYsl).2
  set X := X₀ ∪ (domain X₀ Y₀ \ {c | c.toInt ∈ T}) with hX
  have hXsl : IsSemilinearSet X :=
    h.semilinear_left.union (hD₀.sdiff hT.isSemilinearSet_nat)
  have hsep : V.Separator X Y := by
    refine ⟨hXsl, hYsl, fun x hx y hy hxy => ?_⟩
    rcases hx with hx | ⟨hxD, hxT⟩
    · exact hsep₁.no_run x hx y hy hxy
    · exact hxT (hT.subset ⟨x, ⟨⟨y, hy, hxy⟩, hxD⟩, rfl⟩)
  refine ⟨X, Y, hsep, Set.subset_union_left, Set.subset_union_left, ?_⟩
  have hdom : toIntSet (domain X Y) ⊆ S ∩ T := by
    rintro _ ⟨c, hc, rfl⟩
    simp only [domain, hX, hY, Set.mem_compl_iff, Set.mem_union, not_or, Set.mem_sdiff,
      Set.mem_ofPred_eq, not_and, not_not] at hc
    obtain ⟨⟨hcX, hcT⟩, hcY, hcS⟩ := hc
    exact ⟨hcS ⟨hcX, hcY⟩, hcT ⟨hcX, hcY⟩⟩
  refine lt_of_le_of_lt (dim_mono hdom) ?_
  have hne : dim (toIntSet (domain X₀ Y₀)) ≠ ⊥ := by
    rw [Ne, dim_eq_bot_iff]
    obtain ⟨c, hc⟩ := hD
    exact Set.nonempty_iff_ne_empty.1 ⟨c.toInt, c, hc, rfl⟩
  by_cases hH : toIntSet (V.post X₀ ∩ domain X₀ Y₀) = ∅
  · rw [hS.eq_empty hH, Set.empty_inter, dim_empty]
    exact bot_lt_iff_ne_bot.2 hne
  by_cases hK : toIntSet (V.pre Y ∩ domain X₀ Y₀) = ∅
  · rw [hT.eq_empty hK, Set.inter_empty, dim_empty]
    exact bot_lt_iff_ne_bot.2 hne
  have hdisj : toIntSet (V.post X₀ ∩ domain X₀ Y₀) ∩ toIntSet (V.pre Y ∩ domain X₀ Y₀) = ∅ := by
    refine Set.eq_empty_of_forall_notMem ?_
    rintro _ ⟨⟨c, ⟨⟨x, hx, hxc⟩, -⟩, rfl⟩, ⟨c', ⟨⟨y, hy, hc'y⟩, -⟩, hcc'⟩⟩
    obtain rfl := VASConfig.toInt_injective hcc'
    exact hsep₁.no_run x hx y hy (hxc.trans hc'y)
  refine (dim_inter_linearizations_lt hS hT (Set.nonempty_iff_ne_empty.2 hH)
    (Set.nonempty_iff_ne_empty.2 hK) hdisj).trans_le (dim_mono ?_)
  rintro _ (⟨c, ⟨-, hc⟩, rfl⟩ | ⟨c, ⟨-, hc⟩, rfl⟩)
  · exact ⟨c, hc, rfl⟩
  · exact ⟨c, hc, rfl⟩

/-- Every separator is contained in a separator with empty domain (Theorem 9.2, core). -/
theorem separator_complete [Finite ι] {X₀ Y₀ : Set (VASConfig ι)} (h : V.Separator X₀ Y₀) :
    ∃ X Y : Set (VASConfig ι), V.Separator X Y ∧ X₀ ⊆ X ∧ Y₀ ⊆ Y ∧ domain X Y = ∅ := by
  suffices key : ∀ d : WithBot ℕ, ∀ X₀ Y₀ : Set (VASConfig ι), V.Separator X₀ Y₀ →
      dim (toIntSet (domain X₀ Y₀)) = d →
      ∃ X Y : Set (VASConfig ι), V.Separator X Y ∧ X₀ ⊆ X ∧ Y₀ ⊆ Y ∧ domain X Y = ∅ from
    key _ X₀ Y₀ h rfl
  intro d
  induction d using WellFoundedLT.induction with
  | _ d ih =>
    intro X₀ Y₀ h hd
    by_cases hD : (domain X₀ Y₀).Nonempty
    · obtain ⟨X, Y, hXY, hX, hY, hlt⟩ := separator_improve h hD
      obtain ⟨X', Y', h', hX', hY', hE⟩ := ih _ (hd ▸ hlt) X Y hXY rfl
      exact ⟨X', Y', h', hX.trans hX', hY.trans hY', hE⟩
    · exact ⟨X₀, Y₀, h, subset_rfl, subset_rfl, Set.not_nonempty_iff_eq_empty.1 hD⟩

/-- **Theorem 9.2** (Leroux): if `y` is not reachable from `x`, there is a Presburger forward
inductive invariant containing `x` and not `y`. -/
theorem exists_semilinear_invariant [Finite ι] {x y : VASConfig ι} (h : ¬ V.Reach x y) :
    ∃ X : Set (VASConfig ι), IsSemilinearSet X ∧ V.IsInductive X ∧ x ∈ X ∧ y ∉ X := by
  have hsep : V.Separator {x} {y} := by
    refine ⟨.singleton x, .singleton y, ?_⟩
    rintro a rfl b rfl
    exact h
  obtain ⟨X, Y, hXY, hx, hy, hE⟩ := separator_complete hsep
  obtain ⟨hind, -, hdisj⟩ := hXY.inductive_of_domain_empty hE
  refine ⟨X, hXY.semilinear_left, hind, hx rfl, fun hyX => ?_⟩
  exact Set.disjoint_left.1 hdisj hyX (hy rfl)

/-- `y` is not reachable from `x` iff a Presburger inductive invariant separates them. -/
theorem not_reach_iff [Finite ι] {x y : VASConfig ι} :
    ¬ V.Reach x y ↔
      ∃ X : Set (VASConfig ι), IsSemilinearSet X ∧ V.IsInductive X ∧ x ∈ X ∧ y ∉ X := by
  refine ⟨exists_semilinear_invariant, ?_⟩
  rintro ⟨X, -, hX, hx, hy⟩
  exact not_reach_of_isInductive hX hx hy

end VAS

end Cslib
