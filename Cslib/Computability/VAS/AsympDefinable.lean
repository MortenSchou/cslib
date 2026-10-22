/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Periodic
public import Cslib.Foundations.Data.RatDefinable.FourierMotzkin
public import Mathlib.Algebra.Group.Submonoid.Finsupp
public import Mathlib.Algebra.Module.Pi
public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Algebra.BigOperators.GroupWithZero.Action
public import Mathlib.Algebra.BigOperators.Pi
public import Mathlib.Tactic.LinearCombination

/-!
# Periodic sets and asymptotic definability

A set `P ⊆ ℤ^κ` is *periodic* if it contains `0` and is closed under addition. It is
*asymptotically definable* if the rational cone `ℚ≥0 P` it generates is rationally definable
(a finite union of systems of homogeneous linear inequalities, `RatDefinable`).

## Main definitions

* `Cslib.VAS.AsympDefinable`: asymptotically definable sets.
* `Cslib.VAS.relComp`: composition of relations encoded as vectors of `ℤ^(ι ⊕ ι)`.

## Main results

* `Cslib.VAS.mem_ratCone_iff`: for periodic `P`, `v ∈ ℚ≥0 P` iff some positive multiple of `v` is
  (the image of) an element of `P`.
* `Cslib.VAS.asympDefinable_of_fg`: finitely generated periodic sets are asymptotically
  definable.
* `Cslib.VAS.AsympDefinable.inter`: closure under intersection (Leroux, Lemma 6.2).
* `Cslib.VAS.AsympDefinable.relComp`: closure under relational composition (Leroux, Lemma 5.1).

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib.VAS

variable {κ : Type*}

/-- `P` is *asymptotically definable* if `ℚ≥0 P` is rationally definable. -/
def AsympDefinable [Fintype κ] (P : Set (κ → ℤ)) : Prop := RatDefinable (ratCone P)

section RatVec

@[simp] theorem ratVec_zero : ratVec (0 : κ → ℤ) = 0 := by
  funext i
  simp [ratVec]

@[simp] theorem ratVec_add (x y : κ → ℤ) : ratVec (x + y) = ratVec x + ratVec y := by
  funext i
  simp [ratVec]

@[simp] theorem ratVec_sub (x y : κ → ℤ) : ratVec (x - y) = ratVec x - ratVec y := by
  funext i
  simp [ratVec]

@[simp] theorem ratVec_neg (x : κ → ℤ) : ratVec (-x) = -ratVec x := by
  funext i
  simp [ratVec]

theorem ratVec_nsmul (n : ℕ) (x : κ → ℤ) : ratVec (n • x) = (n : ℚ) • ratVec x := by
  funext i
  simp [ratVec]

theorem ratVec_zsmul (n : ℤ) (x : κ → ℤ) : ratVec (n • x) = (n : ℚ) • ratVec x := by
  funext i
  simp [ratVec]

theorem ratVec_injective : Function.Injective (ratVec : (κ → ℤ) → κ → ℚ) := fun x y h =>
  funext fun i => by simpa [ratVec] using congrFun h i

theorem ratVec_sum {α : Type*} (s : Finset α) (f : α → κ → ℤ) :
    ratVec (∑ a ∈ s, f a) = ∑ a ∈ s, ratVec (f a) := by
  funext i
  simp [ratVec]

end RatVec

section Cone

variable {P : Set (κ → ℤ)}

theorem ratCone_mono {P Q : Set (κ → ℤ)} (h : P ⊆ Q) : ratCone P ⊆ ratCone Q :=
  fun _ ⟨q, hq, p, hp, hv⟩ => ⟨q, hq, p, h hp, hv⟩

theorem ratVec_mem_ratCone {p : κ → ℤ} (hp : p ∈ P) : ratVec p ∈ ratCone P :=
  ⟨1, zero_le_one, p, hp, (one_smul _ _).symm⟩

/-- For a periodic `P`, `v ∈ ℚ≥0 P` iff some positive natural multiple of `v` is an element
of `P`. -/
theorem mem_ratCone_iff (hP : IsPeriodic P) {v : κ → ℚ} :
    v ∈ ratCone P ↔ ∃ n : ℕ, 0 < n ∧ ∃ p ∈ P, (n : ℚ) • v = ratVec p := by
  constructor
  · rintro ⟨q, hq, p, hp, rfl⟩
    refine ⟨q.den, q.den_pos, q.num.toNat • p, hP.nsmul_mem hp _, ?_⟩
    rw [ratVec_nsmul, smul_smul]
    congr 1
    have h1 : (q.num.toNat : ℚ) = q.num := by
      exact_mod_cast Int.toNat_of_nonneg (Rat.num_nonneg.2 hq)
    rw [h1, mul_comm, Rat.mul_den_eq_num]
  · rintro ⟨n, hn, p, hp, h⟩
    refine ⟨(n : ℚ)⁻¹, by positivity, p, hp, ?_⟩
    rw [← h, smul_smul, inv_mul_cancel₀ (by exact_mod_cast hn.ne'), one_smul]

/-- Integer-vector version of `mem_ratCone_iff`. -/
theorem ratVec_mem_ratCone_iff (hP : IsPeriodic P) {z : κ → ℤ} :
    ratVec z ∈ ratCone P ↔ ∃ n : ℕ, 0 < n ∧ n • z ∈ P := by
  rw [mem_ratCone_iff hP]
  constructor
  · rintro ⟨n, hn, p, hp, h⟩
    refine ⟨n, hn, ?_⟩
    have : n • z = p := ratVec_injective (by rw [ratVec_nsmul]; exact h)
    rwa [this]
  · rintro ⟨n, hn, h⟩
    exact ⟨n, hn, _, h, (ratVec_nsmul n z).symm⟩

theorem ratCone_zero_mem (hP : IsPeriodic P) : (0 : κ → ℚ) ∈ ratCone P :=
  ⟨0, le_rfl, 0, hP.1, by simp only [zero_smul]⟩

theorem ratCone_add_mem (hP : IsPeriodic P) {a b : κ → ℚ} (ha : a ∈ ratCone P)
    (hb : b ∈ ratCone P) : a + b ∈ ratCone P := by
  rw [mem_ratCone_iff hP] at *
  obtain ⟨n, hn, p, hp, h⟩ := ha
  obtain ⟨m, hm, r, hr, h'⟩ := hb
  refine ⟨n * m, Nat.mul_pos hn hm, m • p + n • r,
    hP.2 _ (hP.nsmul_mem hp _) _ (hP.nsmul_mem hr _), ?_⟩
  rw [ratVec_add, ratVec_nsmul, ratVec_nsmul, ← h, ← h', smul_add, smul_smul, smul_smul,
    Nat.cast_mul, mul_comm (n : ℚ) m]

theorem ratCone_add_mem_of_mem (hP : IsPeriodic P) {a : κ → ℚ} (ha : a ∈ ratCone P)
    {p : κ → ℤ} (hp : p ∈ P) : a + ratVec p ∈ ratCone P :=
  ratCone_add_mem hP ha (ratVec_mem_ratCone hp)

theorem ratCone_sum_mem (hP : IsPeriodic P) {α : Type*} (s : Finset α) (f : α → κ → ℚ)
    (h : ∀ a ∈ s, f a ∈ ratCone P) : ∑ a ∈ s, f a ∈ ratCone P :=
  (IsPeriodic.sum_mem ⟨ratCone_zero_mem hP, fun _ ha _ hb => ratCone_add_mem hP ha hb⟩) s f h

/-- Intersection of the cones of two periodic sets is the cone of their intersection. -/
theorem ratCone_inter {P₁ P₂ : Set (κ → ℤ)} (h₁ : IsPeriodic P₁) (h₂ : IsPeriodic P₂) :
    ratCone (P₁ ∩ P₂) = ratCone P₁ ∩ ratCone P₂ := by
  refine Set.Subset.antisymm (fun v hv => ⟨ratCone_mono Set.inter_subset_left hv,
    ratCone_mono Set.inter_subset_right hv⟩) ?_
  rintro v ⟨hv₁, hv₂⟩
  rw [mem_ratCone_iff h₁] at hv₁
  rw [mem_ratCone_iff h₂] at hv₂
  obtain ⟨n₁, hn₁, p₁, hp₁, e₁⟩ := hv₁
  obtain ⟨n₂, hn₂, p₂, hp₂, e₂⟩ := hv₂
  rw [mem_ratCone_iff (h₁.inter h₂)]
  refine ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂, n₂ • p₁, ⟨h₁.nsmul_mem hp₁ _, ?_⟩, ?_⟩
  · have : n₂ • p₁ = n₁ • p₂ := by
      apply ratVec_injective
      rw [ratVec_nsmul, ratVec_nsmul, ← e₁, ← e₂, smul_smul, smul_smul, mul_comm]
    rw [this]
    exact h₂.nsmul_mem hp₂ _
  · rw [ratVec_nsmul, ← e₁, smul_smul, Nat.cast_mul, mul_comm]

/-- Intersection of asymptotically definable periodic sets (Leroux, Lemma 6.2): the cone of the
intersection is the intersection of the cones, by scaling with a common multiple. -/
theorem AsympDefinable.inter [Fintype κ] {P₁ P₂ : Set (κ → ℤ)} (h₁ : IsPeriodic P₁)
    (h₂ : IsPeriodic P₂) (d₁ : AsympDefinable P₁) (d₂ : AsympDefinable P₂) :
    IsPeriodic (P₁ ∩ P₂) ∧ AsympDefinable (P₁ ∩ P₂) :=
  ⟨h₁.inter h₂, by rw [AsympDefinable, ratCone_inter h₁ h₂]; exact RatDefinable.inter d₁ d₂⟩

end Cone

section FG

variable [Fintype κ]

omit [Fintype κ] in
theorem isPeriodic_closure (s : Set (κ → ℤ)) : IsPeriodic (AddSubmonoid.closure s : Set (κ → ℤ)) :=
  isPeriodic_coe _

omit [Fintype κ] in
/-- The cone of a finitely generated periodic set is the set of nonnegative rational combinations
of the generators. -/
theorem ratCone_closure_eq (s : Finset (κ → ℤ)) :
    ratCone (AddSubmonoid.closure (s : Set (κ → ℤ)) : Set (κ → ℤ)) =
      {v | ∃ w : s → ℚ, (∀ i, 0 ≤ w i) ∧ v = ∑ i, w i • ratVec i.1} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro v ⟨q, hq, p, hp, rfl⟩
    obtain ⟨a, rfl⟩ := AddSubmonoid.mem_closure_finset'.1 hp
    refine ⟨fun i => q * a i, fun i => by positivity, ?_⟩
    simp only [ratVec_sum, ratVec_nsmul, Finset.smul_sum, smul_smul]
  · rintro v ⟨w, hw, rfl⟩
    refine ratCone_sum_mem (isPeriodic_closure _) _ _ fun i _ => ?_
    exact ⟨w i, hw i, i.1, AddSubmonoid.subset_closure i.2, rfl⟩

/-- Finitely generated periodic sets are asymptotically definable: the cone is the projection of
a polyhedron in the generator coefficients. -/
theorem asympDefinable_of_fg (s : Finset (κ → ℤ)) :
    AsympDefinable (AddSubmonoid.closure (s : Set (κ → ℤ)) : Set (κ → ℤ)) := by
  classical
  unfold AsympDefinable
  rw [ratCone_closure_eq]
  -- the polyhedron in the variables `(v, w)`: `w ≥ 0` and `v k = ∑ i, w i * i k`
  let a : κ → κ ⊕ s → ℤ := fun k => Sum.elim (Pi.single k 1) fun i => -i.1 k
  convert ((RatDefinable.forall_fintype fun i : s => RatDefinable.coord_nonneg (Sum.inr i)).inter
    (RatDefinable.forall_fintype fun k => RatDefinable.zero (a k))).proj (κ' := s) using 1
  ext v
  refine exists_congr fun w => ?_
  simp only [a, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.single_apply, Int.cast_ite,
    Int.cast_one, Int.cast_zero, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ,
    ite_true, Int.cast_neg, neg_mul, Finset.sum_neg_distrib, ← sub_eq_add_neg, sub_eq_zero,
    Set.mem_inter_iff, Set.mem_ofPred_eq, funext_iff, Finset.sum_apply, Pi.smul_apply, ratVec,
    smul_eq_mul, mul_comm (w _)]

end FG

section RelComp

variable {ι : Type*}

/-- Relation composition on relations encoded as vectors in `ℤ^(ι ⊕ ι)`. -/
def relComp (R S : Set (ι ⊕ ι → ℤ)) : Set (ι ⊕ ι → ℤ) :=
  {w | ∃ z : ι → ℤ, Sum.elim (fun i => w (Sum.inl i)) z ∈ R ∧
    Sum.elim z (fun i => w (Sum.inr i)) ∈ S}

theorem isPeriodic_relComp {R S : Set (ι ⊕ ι → ℤ)} (hR : IsPeriodic R) (hS : IsPeriodic S) :
    IsPeriodic (relComp R S) := by
  refine ⟨⟨0, ?_, ?_⟩, ?_⟩
  · convert hR.1 using 1
    exact Sum.elim_zero_zero
  · convert hS.1 using 1
    exact Sum.elim_zero_zero
  · rintro w ⟨z, hz₁, hz₂⟩ w' ⟨z', hz₁', hz₂'⟩
    have h₁ := hR.2 _ hz₁ _ hz₁'
    have h₂ := hS.2 _ hz₂ _ hz₂'
    rw [← Sum.elim_add_add] at h₁ h₂
    exact ⟨z + z', h₁, h₂⟩

/-- The cone of a composition of periodic relations is the composition of the cones. -/
theorem ratCone_relComp {R S : Set (ι ⊕ ι → ℤ)} (hR : IsPeriodic R) (hS : IsPeriodic S) :
    ratCone (relComp R S) = {v : ι ⊕ ι → ℚ | ∃ z : ι → ℚ,
      Sum.elim (fun i => v (Sum.inl i)) z ∈ ratCone R ∧
      Sum.elim z (fun i => v (Sum.inr i)) ∈ ratCone S} := by
  ext v
  constructor
  · rintro ⟨q, hq, w, ⟨z, hz₁, hz₂⟩, rfl⟩
    refine ⟨q • ratVec z, ⟨q, hq, _, hz₁, ?_⟩, ⟨q, hq, _, hz₂, ?_⟩⟩ <;>
      (ext (i | i) <;> simp [ratVec])
  · rintro ⟨z, hz₁, hz₂⟩
    obtain ⟨n₁, hn₁, r, hr, e₁⟩ := (mem_ratCone_iff hR).1 hz₁
    obtain ⟨n₂, hn₂, t, ht, e₂⟩ := (mem_ratCone_iff hS).1 hz₂
    have a (i) := congrFun e₁ (Sum.inl i)
    have b (i) := congrFun e₁ (Sum.inr i)
    have c (i) := congrFun e₂ (Sum.inl i)
    have d (i) := congrFun e₂ (Sum.inr i)
    simp only [Sum.elim_inl, Sum.elim_inr, Pi.smul_apply, smul_eq_mul, ratVec] at a b c d
    have hmid (i) : (n₂ : ℤ) * r (Sum.inr i) = n₁ * t (Sum.inl i) := by
      have : (((n₂ : ℤ) * r (Sum.inr i) : ℤ) : ℚ) = (((n₁ : ℤ) * t (Sum.inl i) : ℤ) : ℚ) := by
        push_cast
        rw [← b, ← c]
        ring
      exact_mod_cast this
    refine (mem_ratCone_iff (isPeriodic_relComp hR hS)).2 ⟨n₁ * n₂, Nat.mul_pos hn₁ hn₂,
      Sum.elim (n₂ • fun i => r (Sum.inl i)) (n₁ • fun i => t (Sum.inr i)),
      ⟨n₂ • fun i => r (Sum.inr i), ?_, ?_⟩, ?_⟩
    · convert hR.nsmul_mem hr n₂ using 1
      ext (i | i) <;> simp
    · convert hS.nsmul_mem ht n₁ using 1
      ext (i | i) <;> simp [hmid i]
    · ext (i | i) <;>
        simp only [ratVec, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, Pi.mul_apply, Pi.natCast_apply,
          Sum.elim_inl, Sum.elim_inr] <;>
        push_cast
      · linear_combination (n₂ : ℚ) * a i
      · linear_combination (n₁ : ℚ) * d i

/-- Asymptotically definable periodic relations are stable under composition (Leroux, Lemma 5.1). -/
theorem AsympDefinable.relComp [Fintype ι] {R S : Set (ι ⊕ ι → ℤ)}
    (hR : IsPeriodic R) (hS : IsPeriodic S) (dR : AsympDefinable R) (dS : AsympDefinable S) :
    IsPeriodic (relComp R S) ∧ AsympDefinable (relComp R S) := by
  refine ⟨isPeriodic_relComp hR hS, ?_⟩
  unfold AsympDefinable at *
  rw [ratCone_relComp hR hS]
  let eR : ι ⊕ ι → (ι ⊕ ι) ⊕ ι := Sum.elim (fun i => Sum.inl (Sum.inl i)) Sum.inr
  let eS : ι ⊕ ι → (ι ⊕ ι) ⊕ ι := Sum.elim Sum.inr (fun i => Sum.inl (Sum.inr i))
  have hC := (dR.comap eR).inter (dS.comap eS)
  convert hC.proj (κ' := ι) using 1
  ext v
  simp only [Set.mem_ofPred_eq, Set.mem_inter_iff]
  refine exists_congr fun z => ?_
  have e₁ : (fun i => Sum.elim v z (eR i)) = Sum.elim (fun i => v (Sum.inl i)) z := by
    ext (_ | _) <;> rfl
  have e₂ : (fun i => Sum.elim v z (eS i)) = Sum.elim z (fun i => v (Sum.inr i)) := by
    ext (_ | _) <;> rfl
  rw [e₁, e₂]

end RelComp

end Cslib.VAS
