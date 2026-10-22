/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.TransformerRel
public import Mathlib.RingTheory.Localization.Integer
public import Mathlib.RingTheory.Localization.Rat

/-! # The relation `R_γ` is contained in the cone of the transformer relation

This file proves Leroux's Lemma 5.15: `R_γ ⊆ ℚ≥0 ▷_c`. Given a point of `R_γ`, a common
denominator and a large multiple turn it into integral data; Euler's lemma provides a total cycle
of the production graph, and a pumping argument fires this cycle from `c + m h₀` for a large `m`,
where `h₀` is a total intraproduction.

## Main results

* `VAS.Triple.R_subset_ratCone`: `R_γ ⊆ ℚ≥0 ▷_c`.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

/-- Finitely many non-negative rationals have a common denominator. -/
theorem exists_common_den {κ : Type*} [Finite κ] (q : κ → ℚ) (hq : ∀ j, 0 ≤ q j) :
    ∃ D : ℕ, 0 < D ∧ ∃ N : κ → ℕ, ∀ j, (D : ℚ) * q j = N j := by
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite (nonZeroDivisors ℤ) q
  choose n hn using hb
  refine ⟨(b : ℤ).natAbs, Int.natAbs_pos.2 (nonZeroDivisors.coe_ne_zero b),
    fun j => (n j).natAbs, fun j => ?_⟩
  have h : (n j : ℚ) = (b : ℤ) * q j := by simpa using hn j
  simp only [Nat.cast_natAbs, Int.cast_abs, h, abs_mul, abs_of_nonneg (hq j)]

/-- Finitely many non-negative rationals `v j` become natural numbers after multiplication by a
common integer `M`, which can be chosen so that the products dominate given natural numbers `a j`
(strictly where `v j` is positive), provided `a j` vanishes where `v j` does. -/
theorem exists_nat_mul {κ : Type*} [Finite κ] (v : κ → ℚ) (hv : ∀ j, 0 ≤ v j) (a : κ → ℕ)
    (ha : ∀ j, v j = 0 → a j = 0) :
    ∃ M : ℕ, 0 < M ∧ ∀ j, ∃ m : ℕ, (m : ℚ) = M * v j ∧ a j ≤ m ∧ (0 < v j → a j < m) := by
  have := Fintype.ofFinite κ
  obtain ⟨D, hD, N, hN⟩ := exists_common_den v hv
  refine ⟨(∑ k, a k + 1) * D, Nat.mul_pos (Nat.succ_pos _) hD, fun j => ?_⟩
  refine ⟨(∑ k, a k + 1) * N j, by push_cast; rw [mul_assoc, hN], ?_⟩
  rcases (hv j).eq_or_lt with h | h
  · simp [ha j h.symm, ← h]
  · have hN1 : 0 < N j := by
      have : (0 : ℚ) < N j := by rw [← hN j]; positivity
      exact_mod_cast this
    have : a j ≤ ∑ k, a k := Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact ⟨by nlinarith, fun _ => by nlinarith⟩

variable {ι : Type*}

namespace VAS

/-- The actions of a VAS are bounded. -/
theorem exists_bound [Finite ι] (V : VAS ι) : ∃ B : ℕ, ∀ a ∈ V.acts, ∀ i, (a i).natAbs ≤ B :=
  have := Fintype.ofFinite ι
  ⟨V.acts.sup fun a => Finset.univ.sup fun i => (a i).natAbs, fun a ha i =>
    (Finset.le_sup (f := fun i => (a i).natAbs) (Finset.mem_univ i)).trans
      (Finset.le_sup (f := fun a : ι → ℤ => Finset.univ.sup fun i => (a i).natAbs) ha)⟩

/-- Pumping a cycle: iterating a run `p ⟶* p'` with `p' + u₀ = p + v₀` turns `k` copies of `u₀`
into `k` copies of `v₀`. -/
theorem reach_pump {V : VAS ι} {p p' u₀ v₀ : VASConfig ι} (h : V.Reach p p')
    (hp : p' + u₀ = p + v₀) (k : ℕ) (w : VASConfig ι) :
    V.Reach (p + k • u₀ + w) (p + k • v₀ + w) := by
  induction k generalizing w with
  | zero => simp only [zero_smul, add_zero]; exact Reach.refl
  | succ k ih =>
    have h1 : V.Reach (p + (k + 1) • u₀ + w) (p + v₀ + k • u₀ + w) :=
      reach_cast (Reach.add_left h (u₀ + k • u₀ + w)) (by rw [succ_nsmul]; abel)
        (by rw [← hp]; abel)
    have h2 := ih (v₀ + w)
    exact h1.trans (reach_cast h2 (by abel) (by rw [succ_nsmul]; abel))

namespace Triple

variable {V : VAS ι} (γ : Triple V)

/-- A path of `G_γ` can be fired from any configuration which agrees with its source state on the
bounded components and is large enough on the unbounded ones. -/
theorem reach_of_path {B : ℕ} (hB : ∀ a ∈ V.acts, ∀ i, (a i).natAbs ≤ B) {s s' : VASConfig ι}
    {ρ : List γ.graph.trans} (hρ : γ.graph.IsPath s ρ s') :
    ∀ p : VASConfig ι, (∀ i ∈ γ.bounded, p i = s i) → (∀ i ∉ γ.bounded, ρ.length * B ≤ p i) →
      ∃ p', V.Reach p p' ∧ p'.toInt = p.toInt + (ρ.map γ.graph.act).sum := by
  induction hρ with
  | nil s => intro p _ _; exact ⟨p, Reach.refl, by simp only [List.map_nil,
      List.sum_nil, add_zero]⟩
  | cons t hrest ih =>
    intro p hp1 hp2
    have hacts := graph_act_mem γ t
    have hnn : ∀ i, 0 ≤ p.toInt i + γ.graph.act t i := by
      intro i
      by_cases hi : i ∈ γ.bounded
      · have := graph_tgt_apply γ t hi
        simp only [VASConfig.toInt, hp1 i hi]
        omega
      · have h1 := hp2 i hi
        have h2 := hB _ hacts i
        simp only [List.length_cons, VASConfig.toInt] at h1 ⊢
        rw [Nat.succ_mul] at h1
        omega
    let q : VASConfig ι := fun i => (p.toInt i + γ.graph.act t i).toNat
    have hq : q.toInt = p.toInt + γ.graph.act t := by
      funext i
      simp only [VASConfig.toInt, q, Pi.add_apply]
      exact Int.toNat_of_nonneg (hnn i)
    have hqi : ∀ i, (q i : ℤ) = p i + γ.graph.act t i := fun i => congrFun hq i
    obtain ⟨p', hp', hp'sum⟩ := ih q (fun i hi => by
      have := graph_tgt_apply γ t hi
      have := hqi i
      rw [hp1 i hi] at this
      omega) (fun i hi => by
      have h1 := hp2 i hi
      have h2 := hB _ hacts i
      have := hqi i
      simp only [List.length_cons] at h1
      rw [Nat.succ_mul] at h1
      omega)
    refine ⟨p', LTS.CanReach.head ⟨_, hacts, hq⟩ hp', ?_⟩
    rw [hp'sum, hq]
    simp only [List.map_cons, List.sum_cons]
    abel

/-- Pumping a cycle of `G_γ`. Let `c + n x ⟶* c + h₀ ⟶* c + n y` with `h₀` positive exactly on the
unbounded components, and let `ρ` be a cycle at the special state with displacement `v₀ - u₀`.
Firing `ρ` from `c + k h₀` for large `k` gives a run from `c + k (n x + u₀)` to
`c + k (n y + v₀)`. -/
theorem exists_reach_of_cycle [Finite ι] {n : ℕ} {h₀ u₀ v₀ : VASConfig ι}
    (hr1 : V.Reach (γ.c + n • γ.x) (γ.c + h₀)) (hr2 : V.Reach (γ.c + h₀) (γ.c + n • γ.y))
    (hb : γ.bounded = {i | h₀ i = 0}) {ρ : List γ.graph.trans}
    (hρ : γ.graph.IsPath γ.special ρ γ.special)
    (hS : ∀ i, (ρ.map γ.graph.act).sum i = v₀ i - u₀ i) :
    ∃ k : ℕ, 0 < k ∧ V.Reach (γ.c + k • (n • γ.x + u₀)) (γ.c + k • (n • γ.y + v₀)) := by
  obtain ⟨B, hB⟩ := exists_bound V
  have hh₀ (i : ι) : i ∈ γ.bounded ↔ h₀ i = 0 := by rw [hb]; rfl
  have hp1 : ∀ i ∈ γ.bounded, (γ.c + (ρ.length * B + 1) • h₀) i = γ.special i := fun i hi => by
    simp [(hh₀ i).1 hi, special, proj_apply_of_mem γ _ hi]
  have hp2 : ∀ i ∉ γ.bounded, ρ.length * B ≤ (γ.c + (ρ.length * B + 1) • h₀) i := fun i hi => by
    have : 1 ≤ h₀ i := Nat.pos_of_ne_zero fun h => hi ((hh₀ i).2 h)
    have := Nat.mul_le_mul_left (ρ.length * B + 1) this
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    omega
  obtain ⟨p', hpp', hp'int⟩ := reach_of_path γ hB hρ _ hp1 hp2
  have hp'eq : p' + u₀ = (γ.c + (ρ.length * B + 1) • h₀) + v₀ := by
    funext i
    have h1 := congrFun hp'int i
    have h2 := hS i
    simp only [VASConfig.toInt, Pi.add_apply] at h1
    simp only [Pi.add_apply]
    omega
  refine ⟨ρ.length * B + 1, Nat.succ_pos _, ?_⟩
  set k := ρ.length * B + 1
  have hA : V.Reach (γ.c + k • (n • γ.x + u₀)) (γ.c + k • h₀ + k • u₀) :=
    reach_cast (Reach.add_left (reach_nsmul hr1 k) (k • u₀)) (by rw [smul_add, smul_smul]; abel)
      (by abel)
  have hC : V.Reach (γ.c + k • h₀ + k • v₀) (γ.c + k • (n • γ.y + v₀)) :=
    reach_cast (Reach.add_left (reach_nsmul hr2 k) (k • v₀)) (by abel)
      (by rw [smul_add, smul_smul]; abel)
  exact hA.trans ((reach_cast (reach_pump hpp' hp'eq k 0) (add_zero _) (add_zero _)).trans hC)

/-- **Lemma 5.15**: `R_γ ⊆ ℚ≥0 ▷_c`. -/
theorem R_subset_ratCone [Finite ι] : γ.R ⊆ ratCone (V.transSet γ.c) := by
  have := Fintype.ofFinite ι
  rintro w ⟨hnn, hsx, hsy, f, hfpos, hK, hdisp⟩
  have := (graph_finite γ).2.fintype
  let _ : DecidableEq γ.graph.trans := Classical.decEq _
  -- a total intraproduction `h₀` and the cycles `ρ₁`, `ρ₂` of its two runs
  obtain ⟨h₀, ⟨n, hr1, hr2⟩, hb⟩ := exists_intraprod_support γ
  have hx : V.Reach (γ.c + n • γ.x) (γ.c + n • γ.y) := hr1.trans hr2
  have hpx := proj_add_intraprod γ (nsmul_x_mem_intraprod γ hx)
  have hpy := proj_add_intraprod γ (nsmul_y_mem_intraprod γ hx)
  have hph := proj_add_intraprod γ (show h₀ ∈ γ.intraprod from ⟨n, hr1, hr2⟩)
  obtain ⟨ρ₁, hρ₁, hs₁⟩ := path_of_reach γ hr1 Reach.refl hr2
  obtain ⟨ρ₂, hρ₂, hs₂⟩ := path_of_reach γ hr2 hr1 Reach.refl
  rw [hpx, hph] at hρ₁
  rw [hph, hpy] at hρ₂
  -- integral data: `M w_x = n x + u₀`, `M w_y = n y + v₀`, `M f = ρ₁ + ρ₂ + g`
  obtain ⟨M, hM, hm⟩ := exists_nat_mul (Sum.elim w f : (ι ⊕ ι) ⊕ γ.graph.trans → ℚ)
    (by rintro ((i | i) | t); exacts [(hnn i).1, (hnn i).2, (hfpos t).le])
    (Sum.elim (Sum.elim (fun i => n * γ.x i) fun i => n * γ.y i)
      fun t => γ.graph.parikh ρ₁ t + γ.graph.parikh ρ₂ t) (by
      rintro ((i | i) | t) h <;> simp only [Sum.elim_inl, Sum.elim_inr] at h ⊢
      · by_contra hne
        exact h.not_gt ((hsx i).2 (Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])))
      · by_contra hne
        exact h.not_gt ((hsy i).2 (Nat.pos_of_ne_zero fun h0 => hne (by simp [h0])))
      · exact absurd h (hfpos t).ne')
  choose m hmq hma hmlt using hm
  let u₀ : VASConfig ι := fun i => m (Sum.inl (Sum.inl i)) - n * γ.x i
  let v₀ : VASConfig ι := fun i => m (Sum.inl (Sum.inr i)) - n * γ.y i
  let g : γ.graph.trans → ℕ := fun t =>
    m (Sum.inr t) - (γ.graph.parikh ρ₁ t + γ.graph.parikh ρ₂ t)
  have hu₀ (i : ι) : (u₀ i : ℚ) = M * w (Sum.inl i) - n * γ.x i := by
    have h : n * γ.x i ≤ m (Sum.inl (Sum.inl i)) := hma (Sum.inl (Sum.inl i))
    simp only [u₀, Nat.cast_sub h, hmq]
    simp
  have hv₀ (i : ι) : (v₀ i : ℚ) = M * w (Sum.inr i) - n * γ.y i := by
    have h : n * γ.y i ≤ m (Sum.inl (Sum.inr i)) := hma (Sum.inl (Sum.inr i))
    simp only [v₀, Nat.cast_sub h, hmq]
    simp
  have hg (t : γ.graph.trans) :
      (g t : ℚ) = M * f t - γ.graph.parikh ρ₁ t - γ.graph.parikh ρ₂ t := by
    have h : γ.graph.parikh ρ₁ t + γ.graph.parikh ρ₂ t ≤ m (Sum.inr t) := hma (Sum.inr t)
    simp only [g, Nat.cast_sub h, hmq]
    simp
    ring
  have hgpos (t : γ.graph.trans) : 0 < g t :=
    Nat.sub_pos_of_lt (hmlt (Sum.inr t) (hfpos t))
  -- the total cycle `ρ` of the Kirchhoff function `M f - ρ₁ - ρ₂`
  have hKg : γ.graph.IsKirchhoff fun t => (g t : ℚ) := by
    have : (fun t => (g t : ℚ)) = (M : ℚ) • f - (fun t => (γ.graph.parikh ρ₁ t : ℚ)) -
        fun t => (γ.graph.parikh ρ₂ t : ℚ) := by
      funext t
      simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, hg]
    rw [this]
    exact ((hK.smul M).sub hρ₁.isKirchhoff_parikh).sub hρ₂.isKirchhoff_parikh
  obtain ⟨ρ, hρ, hcnt⟩ := ProdGraph.euler_lemma (graph_wellFormed γ) (graph_stronglyConnected γ)
    g hgpos hKg (special_mem_states γ)
  -- the displacement of `ρ`
  have hS (i : ι) : (((ρ.map γ.graph.act).sum i : ℤ) : ℚ) = v₀ i - u₀ i := by
    have e : (fun t => (γ.graph.parikh ρ t : ℚ)) = (M : ℚ) • f -
        (fun t => (γ.graph.parikh ρ₁ t : ℚ)) - fun t => (γ.graph.parikh ρ₂ t : ℚ) := by
      funext t
      simp only [hcnt, hg, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    have h0 := congrFun (congrArg γ.graph.disp e) i
    rw [ProdGraph.disp_sub, ProdGraph.disp_sub, ProdGraph.disp_smul] at h0
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, ProdGraph.disp_parikh,
      ← congrFun hdisp i] at h0
    have h1 := congrFun hs₁ i
    have h2 := congrFun hs₂ i
    simp only [VASConfig.toInt, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul] at h1 h2
    rw [h0, hu₀, hv₀, h1, h2]
    push_cast
    ring
  -- firing the total cycle
  obtain ⟨k, hk, hreach⟩ := exists_reach_of_cycle γ hr1 hr2 hb hρ
    (fun i => by exact_mod_cast hS i)
  have hk0 : (k : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hk.ne'
  have hM0 : (M : ℚ) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  refine ⟨((k * M : ℕ) : ℚ)⁻¹, inv_nonneg.2 (Nat.cast_nonneg _),
    relVec (k • (n • γ.x + u₀)) (k • (n • γ.y + v₀)), ⟨_, _, rfl, hreach⟩, ?_⟩
  funext j
  rcases j with i | i
  · have h := hu₀ i
    simp only [ratVec, relVec, Sum.elim_inl, VASConfig.toInt, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, Pi.smul_apply]
    push_cast
    field_simp
    linarith
  · have h := hv₀ i
    simp only [ratVec, relVec, Sum.elim_inr, VASConfig.toInt, Pi.smul_apply, Pi.add_apply,
      smul_eq_mul, Pi.smul_apply]
    push_cast
    field_simp
    linarith

end Triple

end VAS

end Cslib
