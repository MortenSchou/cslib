/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.TransformerGraph

/-! # The relation `R_γ` of a triple

The relation `R_γ ⊆ ℚ≥0^ι × ℚ≥0^ι` of Leroux, Section 5.3, defined through Kirchhoff functions of
the production graph `G_γ`, together with its basic properties.

## Main results

* `VAS.Triple.xy_mem_R`: `(x, y) ∈ R_γ` (Lemma 5.14).
* `VAS.Triple.R_subset_ratCone`: `R_γ ⊆ ℚ≥0 ▷_c` (Lemma 5.15).
* `VAS.Triple.R_definable`: `R_γ` is definable in `FO(ℚ; +, ≤)`.
* `VAS.Triple.finite_R`: for a fixed capacity there are finitely many relations `R_γ`.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

namespace VAS

namespace Triple

variable {V : VAS ι} (γ : Triple V)

/-- The relation `R_γ ⊆ ℚ≥0^ι × ℚ≥0^ι`: same supports as `x`, `y` and `v - u = δ(f)` for a strictly
positive Kirchhoff function `f` of `G_γ`. -/
noncomputable def R : Set (ι ⊕ ι → ℚ) :=
  γ.graph.relR {i | 0 < γ.x i} {i | 0 < γ.y i}

/-- Every transition lies on a cycle at the special state whose displacement is a multiple of
`y - x`. -/
theorem exists_cycle_through (t : γ.graph.trans) :
    ∃ (n : ℕ) (ρ : List γ.graph.trans), γ.graph.IsPath γ.special ρ γ.special ∧ t ∈ ρ ∧
      (ρ.map γ.graph.act).sum = n • (γ.y.toInt - γ.x.toInt) := by
  obtain ⟨⟨s, a, s'⟩, hmem⟩ := t
  obtain ⟨q, q', heq, n, h1, hm, h2⟩ := (mem_graph_trans γ).1 hmem
  obtain ⟨rfl, rfl, rfl⟩ := Prod.mk.injEq _ _ _ _ ▸ heq
  have hqy : V.Reach q (γ.c + n • γ.y) := LTS.CanReach.head hm h2
  have hx : V.Reach (γ.c + n • γ.x) (γ.c + n • γ.y) := h1.trans hqy
  obtain ⟨ρa, hρa, hsa⟩ := path_of_reach γ h1 Reach.refl hqy
  obtain ⟨ρb, hρb, hsb⟩ := path_of_reach γ h2 (h1.tail hm) Reach.refl
  rw [proj_add_intraprod γ (nsmul_x_mem_intraprod γ hx)] at hρa
  rw [proj_add_intraprod γ (nsmul_y_mem_intraprod γ hx)] at hρb
  let t : γ.graph.trans := ⟨_, hmem⟩
  refine ⟨n, ρa ++ t :: ρb, hρa.append ((γ.graph.isPath_single t).append hρb),
    List.mem_append_right _ List.mem_cons_self, ?_⟩
  simp only [List.map_append, List.map_cons, List.sum_append, List.sum_cons, hsa, hsb,
    VASConfig.toInt_add, VASConfig.toInt_nsmul, smul_sub, t, ProdGraph.act]
  abel

/-- There is a total cycle at the special state whose displacement is a positive multiple of
`y - x`. -/
theorem exists_total_cycle [Finite ι] :
    ∃ (N : ℕ) (ρ : List γ.graph.trans), 0 < N ∧ γ.graph.IsPath γ.special ρ γ.special ∧
      (∀ t, t ∈ ρ) ∧ (ρ.map γ.graph.act).sum = N • (γ.y.toInt - γ.x.toInt) := by
  classical
  have hx : V.Reach (γ.c + (1 : ℕ) • γ.x) (γ.c + (1 : ℕ) • γ.y) := by
    simpa only [one_smul] using γ.mem
  obtain ⟨ρ₀, hρ₀, hs₀⟩ := path_of_reach γ (n := 1) (p := γ.c + γ.x) (q := γ.c + γ.y) γ.mem
    (by rw [one_smul]) (by rw [one_smul])
  rw [show γ.proj (γ.c + γ.x) = γ.special by
      simpa only [one_smul] using proj_add_intraprod γ (nsmul_x_mem_intraprod γ hx),
    show γ.proj (γ.c + γ.y) = γ.special by
      simpa only [one_smul] using proj_add_intraprod γ (nsmul_y_mem_intraprod γ hx)] at hρ₀
  have := (graph_finite γ).2.fintype
  have key : ∀ s : Finset γ.graph.trans, ∃ (N : ℕ) (ρ : List γ.graph.trans), 0 < N ∧
      γ.graph.IsPath γ.special ρ γ.special ∧ (∀ t ∈ s, t ∈ ρ) ∧
        (ρ.map γ.graph.act).sum = N • (γ.y.toInt - γ.x.toInt) := fun s => by
    induction s using Finset.induction_on with
    | empty =>
      refine ⟨1, ρ₀, Nat.one_pos, hρ₀, by simp, ?_⟩
      rw [hs₀, one_smul, VASConfig.toInt_add, VASConfig.toInt_add]
      abel
    | insert a s _ ih =>
      obtain ⟨N, ρ, hN, hρ, hmem, hsum⟩ := ih
      obtain ⟨n, ρa, hρa, hamem, hsuma⟩ := exists_cycle_through γ a
      refine ⟨N + n, ρ ++ ρa, Nat.add_pos_left hN n, hρ.append hρa, fun t ht => ?_, ?_⟩
      · rcases Finset.mem_insert.1 ht with rfl | ht
        · exact List.mem_append_right _ hamem
        · exact List.mem_append_left _ (hmem t ht)
      · rw [List.map_append, List.sum_append, hsum, hsuma, add_nsmul]
  obtain ⟨N, ρ, hN, hρ, hmem, hsum⟩ := key Finset.univ
  exact ⟨N, ρ, hN, hρ, fun t => hmem t (Finset.mem_univ t), hsum⟩

/-- **Lemma 5.14**: `(x, y) ∈ R_γ`. -/
theorem xy_mem_R [Finite ι] : ratVec (relVec γ.x γ.y) ∈ γ.R := by
  classical
  have := Fintype.ofFinite ι
  obtain ⟨N, ρ, hN, hρ, hmem, hsum⟩ := exists_total_cycle γ
  have := (graph_finite γ).2.to_subtype
  have hNq : (0 : ℚ) < N := Nat.cast_pos.2 hN
  refine ⟨fun i => ⟨?_, ?_⟩, fun i => ?_, fun i => ?_,
    (N : ℚ)⁻¹ • fun t => (γ.graph.parikh ρ t : ℚ), fun t => ?_, hρ.isKirchhoff_parikh.smul _, ?_⟩
  · simp only [ratVec, relVec, Sum.elim_inl, VASConfig.toInt, Int.cast_natCast, Nat.cast_nonneg]
  · simp only [ratVec, relVec, Sum.elim_inr, VASConfig.toInt, Int.cast_natCast, Nat.cast_nonneg]
  · simp only [ratVec, relVec, Sum.elim_inl, VASConfig.toInt, Int.cast_natCast, Nat.cast_pos,
      Set.mem_ofPred_eq]
  · simp only [ratVec, relVec, Sum.elim_inr, VASConfig.toInt, Int.cast_natCast, Nat.cast_pos,
      Set.mem_ofPred_eq]
  · have : 0 < ρ.count t := List.count_pos_iff.2 (hmem t)
    simpa [ProdGraph.parikh, hNq] using this
  · funext i
    rw [ProdGraph.disp_smul, Pi.smul_apply, ProdGraph.disp_parikh, hsum]
    simp [VASConfig.toInt, ratVec, relVec]
    field_simp

/-- `R_γ` is definable in `FO(ℚ; +, ≤, 0)`. -/
theorem R_definable [Fintype ι] : RatDefinable γ.R :=
  have := (graph_finite γ).2.to_subtype
  ProdGraph.relR_definable _ _

/-- For a fixed capacity there are finitely many distinct relations `R_γ`. -/
theorem finite_R [Finite ι] (c : VASConfig ι) :
    {W : Set (ι ⊕ ι → ℚ) | ∃ γ : Triple V, γ.c = c ∧ W = γ.R}.Finite := by
  have hfin : ({G : ProdGraph ι | ∃ γ : Triple V, γ.c = c ∧ G = γ.graph} ×ˢ
      (Set.univ : Set (Set ι × Set ι))).Finite :=
    (finite_prodGraphs c).prod Set.finite_univ
  refine (hfin.image fun p => p.1.relR p.2.1 p.2.2).subset ?_
  rintro _ ⟨γ, hc, rfl⟩
  exact ⟨(γ.graph, {i | 0 < γ.x i}, {i | 0 < γ.y i}), ⟨⟨γ, hc, rfl⟩, Set.mem_univ _⟩, rfl⟩

end Triple

end VAS

end Cslib
