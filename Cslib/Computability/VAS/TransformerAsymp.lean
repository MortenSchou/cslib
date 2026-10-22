/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.TransformerCone

/-! # The cone of a transformer relation is definable

The cone `ℚ≥0 ▷_c` of the transformer relation with capacity `c` is the finite union of the
relations `R_γ` over the triples `γ` with capacity `c` (Leroux, Corollary 5.16). Each `R_γ` is
definable in `FO(ℚ; +, ≤)`, hence so is the cone. In the terminology of the development: the
transformer relation is asymptotically definable.

## Main results

* `VAS.ratCone_transSet_eq`: the cone is the union of the relations `R_γ`.
* `VAS.ratDefinable_ratCone_transSet`: the cone of `▷_c` is definable in `FO(ℚ; +, ≤)`.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

namespace VAS

variable (V : VAS ι)

/-- **Corollary 5.16**: the cone `ℚ≥0 ▷_c` is the union of the relations `R_γ`, `γ` of
capacity `c`. -/
theorem ratCone_transSet_eq [Finite ι] (c : VASConfig ι) :
    ratCone (V.transSet c) =
      {v | ∃ W ∈ {W : Set (ι ⊕ ι → ℚ) | ∃ γ : Triple V, γ.c = c ∧ W = γ.R}, v ∈ W} := by
  have := Fintype.ofFinite ι
  ext v
  constructor
  · rintro ⟨q, hq, _, ⟨x, y, rfl, hxy⟩, rfl⟩
    let γ : Triple V := ⟨x, c, y, hxy⟩
    rcases hq.eq_or_lt with rfl | hq
    · refine ⟨_, ⟨⟨0, c, 0, Reach.refl⟩, rfl, rfl⟩, ?_⟩
      have := Triple.xy_mem_R (⟨0, c, 0, Reach.refl⟩ : Triple V)
      convert this using 1
      funext i
      rcases i with i | i <;> simp only [zero_smul, ratVec, relVec, VASConfig.toInt, Sum.elim_inl,
        Sum.elim_inr, Pi.zero_apply, Nat.cast_zero, Int.cast_zero]
    · have := (Triple.graph_finite γ).2.to_subtype
      exact ⟨_, ⟨γ, rfl, rfl⟩, ProdGraph.relR_smul (G := γ.graph) (Triple.xy_mem_R γ) hq⟩
  · rintro ⟨_, ⟨γ, rfl, rfl⟩, hv⟩
    exact Triple.R_subset_ratCone γ hv

/-- The cone `ℚ≥0 ▷_c` of the transformer relation is definable in `FO(ℚ; +, ≤)`. -/
theorem ratDefinable_ratCone_transSet [Fintype ι] (c : VASConfig ι) :
    RatDefinable (ratCone (V.transSet c)) := by
  have hfin := Triple.finite_R (V := V) c
  have hdef : ∀ W ∈ hfin.toFinset.toList, RatDefinable W := by
    intro W hW
    obtain ⟨γ, -, rfl⟩ := hfin.mem_toFinset.1 (Finset.mem_toList.1 hW)
    exact Triple.R_definable γ
  have := RatDefinable.iUnion_list hfin.toFinset.toList id hdef
  convert this using 1
  rw [ratCone_transSet_eq]
  ext v
  simp only [Set.mem_ofPred_eq, id, Finset.mem_toList, Set.Finite.mem_toFinset]

end VAS

end Cslib
