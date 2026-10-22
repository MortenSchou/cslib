/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.ReachInter
public import Cslib.Computability.VAS.Linearization

/-! # Reachability sets are almost semilinear

The intersection of the reachability relation with a Presburger relation is almost semilinear
(Leroux, Section 6), and so are the sets `post(X) ∩ Y` and `pre(Y) ∩ X` for Presburger `X, Y`
(Corollary 6.3).

## Main results

* `VAS.almostSemilinear_reach_inter`: `→* ∩ R` is almost semilinear for Presburger `R`.
* `VAS.reach_isAlmostSemilinear`: the reachability relation is almost semilinear (POPL Thm 9.1).
* `VAS.almostSemilinear_post_inter`: Corollary 6.3.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

open scoped Pointwise

namespace Cslib

section Semilinear

variable {M : Type*} [AddCommMonoid M]

/-- A semilinear set is a finite union of linear sets `a + P`, `P` finitely generated periodic. -/
theorem semilinear_decomp {R : Set M} (hR : IsSemilinearSet R) :
    ∃ F : Set (M × Finset M), F.Finite ∧
      R = ⋃ p ∈ F, p.1 +ᵥ (AddSubmonoid.closure (p.2 : Set M) : Set M) := by
  classical
  obtain ⟨S, hS, hlin, rfl⟩ := hR
  choose! a t ht using fun s (hs : s ∈ S) => isLinearSet_iff.1 (hlin s hs)
  refine ⟨(fun s => (a s, t s)) '' S, hS.image _, ?_⟩
  rw [Set.sUnion_eq_biUnion, Set.biUnion_image]
  exact Set.iUnion₂_congr fun s hs => ht s hs

/-- Product of semilinear sets is semilinear. -/
theorem isSemilinearSet_prod {N : Type*} [AddCommMonoid N] [AddMonoid.FG M] [AddMonoid.FG N]
    {X : Set M} {Y : Set N} (hX : IsSemilinearSet X) (hY : IsSemilinearSet Y) :
    IsSemilinearSet (X ×ˢ Y) := by
  have : X ×ˢ Y = (AddMonoidHom.fst M N) ⁻¹' X ∩ (AddMonoidHom.snd M N) ⁻¹' Y := rfl
  rw [this]
  exact (hX.preimage _).inter (hY.preimage _)

end Semilinear

namespace VAS

section AlmostSemilinear

variable {κ : Type*} [Fintype κ]

/-- A set is almost semilinear iff it is a finite union of `b + P` with `P` periodic and
asymptotically definable. -/
theorem almostSemilinear_iff {X : Set (κ → ℤ)} :
    AlmostSemilinear X ↔ ∃ F : Set ((κ → ℤ) × Set (κ → ℤ)), F.Finite ∧
      (∀ p ∈ F, IsPeriodic p.2 ∧ AsympDefinable p.2) ∧ X = ⋃ p ∈ F, p.1 +ᵥ p.2 := by
  constructor
  · rintro ⟨S, F, hF, hP, hX, -⟩
    exact ⟨F, hF, hP, hX⟩
  · rintro ⟨F, hF, hP, hX⟩
    exact ⟨_, F, hF, hP, hX, rfl⟩

/-- The empty set is almost semilinear. -/
theorem AlmostSemilinear.empty : AlmostSemilinear (∅ : Set (κ → ℤ)) :=
  almostSemilinear_iff.2 ⟨∅, Set.finite_empty, by simp, by simp⟩

/-- A translate of an asymptotically definable periodic set is almost semilinear. -/
theorem AlmostSemilinear.vadd_periodic (b : κ → ℤ) {P : Set (κ → ℤ)} (hP : IsPeriodic P)
    (hd : AsympDefinable P) : AlmostSemilinear (b +ᵥ P) :=
  almostSemilinear_iff.2 ⟨{(b, P)}, Set.finite_singleton _, by simpa using ⟨hP, hd⟩, by simp⟩

/-- A union of two almost semilinear sets is almost semilinear. -/
theorem AlmostSemilinear.union {X Y : Set (κ → ℤ)} (hX : AlmostSemilinear X)
    (hY : AlmostSemilinear Y) : AlmostSemilinear (X ∪ Y) := by
  obtain ⟨F, hF, hFp, rfl⟩ := almostSemilinear_iff.1 hX
  obtain ⟨G, hG, hGp, rfl⟩ := almostSemilinear_iff.1 hY
  refine almostSemilinear_iff.2 ⟨F ∪ G, hF.union hG, ?_, ?_⟩
  · rintro p (hp | hp)
    exacts [hFp p hp, hGp p hp]
  · rw [Set.biUnion_union]

/-- A finite union of almost semilinear sets is almost semilinear. -/
theorem AlmostSemilinear.biUnion {α : Type*} {s : Set α} (hs : s.Finite) {t : α → Set (κ → ℤ)}
    (h : ∀ a ∈ s, AlmostSemilinear (t a)) : AlmostSemilinear (⋃ a ∈ s, t a) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using AlmostSemilinear.empty
  | insert ha _ ih =>
    rw [Set.biUnion_insert]
    exact (h _ (Set.mem_insert _ _)).union (ih fun a ha' => h a (Set.mem_insert_of_mem _ ha'))

section Projection

variable {κ₁ κ₂ : Type*}

/-- The projection of `ℤ^(κ₁ ⊕ κ₂)` on the first `κ₁` coordinates. -/
def projL : (κ₁ ⊕ κ₂ → ℤ) →+ (κ₁ → ℤ) where
  toFun w i := w (Sum.inl i)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The projection of `ℤ^(κ₁ ⊕ κ₂)` on the last `κ₂` coordinates. -/
def projR : (κ₁ ⊕ κ₂ → ℤ) →+ (κ₂ → ℤ) where
  toFun w i := w (Sum.inr i)
  map_zero' := rfl
  map_add' _ _ := rfl

/-- The image of a periodic set under an additive map is periodic. -/
theorem IsPeriodic.image {E F : Type*} [AddCommMonoid E] [AddCommMonoid F] {P : Set E}
    (hP : IsPeriodic P) (f : E →+ F) : IsPeriodic (f '' P) := by
  refine ⟨⟨0, hP.1, map_zero f⟩, ?_⟩
  rintro _ ⟨p, hp, rfl⟩ _ ⟨q, hq, rfl⟩
  exact ⟨p + q, hP.2 p hp q hq, map_add f p q⟩

/-- The cone of the projection of a periodic set is the projection of its cone. -/
theorem ratCone_projL (P : Set (κ₁ ⊕ κ₂ → ℤ)) :
    ratCone (projL '' P) = {v | ∃ w : κ₂ → ℚ, Sum.elim v w ∈ ratCone P} := by
  ext v
  constructor
  · rintro ⟨q, hq, _, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨q • fun i => (p (Sum.inr i) : ℚ), q, hq, p, hp, ?_⟩
    funext j
    cases j <;> rfl
  · rintro ⟨w, q, hq, p, hp, h⟩
    refine ⟨q, hq, _, ⟨p, hp, rfl⟩, ?_⟩
    funext i
    exact congrFun h (Sum.inl i)

/-- The cone of the projection of a periodic set is the projection of its cone. -/
theorem ratCone_projR (P : Set (κ₁ ⊕ κ₂ → ℤ)) :
    ratCone (projR '' P) = {v | ∃ w : κ₁ → ℚ, Sum.elim w v ∈ ratCone P} := by
  ext v
  constructor
  · rintro ⟨q, hq, _, ⟨p, hp, rfl⟩, rfl⟩
    refine ⟨q • fun i => (p (Sum.inl i) : ℚ), q, hq, p, hp, ?_⟩
    funext j
    cases j <;> rfl
  · rintro ⟨w, q, hq, p, hp, h⟩
    refine ⟨q, hq, _, ⟨p, hp, rfl⟩, ?_⟩
    funext i
    exact congrFun h (Sum.inr i)

/-- The projection of an asymptotically definable periodic set on the first coordinates is
asymptotically definable. -/
theorem AsympDefinable.projL [Fintype κ₁] [Fintype κ₂] {P : Set (κ₁ ⊕ κ₂ → ℤ)}
    (hd : AsympDefinable P) :
    AsympDefinable (projL '' P) := by
  unfold AsympDefinable at *
  rw [ratCone_projL]
  exact hd.proj

/-- The projection of an asymptotically definable periodic set on the last coordinates is
asymptotically definable. -/
theorem AsympDefinable.projR [Fintype κ₁] [Fintype κ₂] {P : Set (κ₁ ⊕ κ₂ → ℤ)}
    (hd : AsympDefinable P) :
    AsympDefinable (projR '' P) := by
  unfold AsympDefinable at *
  rw [ratCone_projR]
  have := (hd.comap (Sum.swap : κ₁ ⊕ κ₂ → κ₂ ⊕ κ₁)).proj (κ' := κ₁)
  convert this using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  refine exists_congr fun w => ?_
  have : (fun i => Sum.elim v w (Sum.swap i)) = Sum.elim w v := by
    funext j
    cases j <;> rfl
  rw [this]

/-- The image of an almost semilinear set under an additive map that preserves asymptotic
definability of periodic sets. -/
theorem AlmostSemilinear.image {E F : Type*} [Fintype E] [Fintype F] {X : Set (E → ℤ)}
    (hX : AlmostSemilinear X) (f : (E → ℤ) →+ (F → ℤ))
    (hf : ∀ P : Set (E → ℤ), AsympDefinable P → AsympDefinable (f '' P)) :
    AlmostSemilinear (f '' X) := by
  obtain ⟨G, hG, hGp, rfl⟩ := almostSemilinear_iff.1 hX
  refine almostSemilinear_iff.2 ⟨(fun p => (f p.1, f '' p.2)) '' G, hG.image _, ?_, ?_⟩
  · rintro _ ⟨p, hp, rfl⟩
    exact ⟨(hGp p hp).1.image f, hf _ (hGp p hp).2⟩
  · rw [Set.biUnion_image, Set.image_iUnion₂]
    refine Set.iUnion₂_congr fun p hp => ?_
    exact Set.image_vadd_distrib f p.1 p.2

end Projection

end AlmostSemilinear

section Reach

variable {ι : Type*} {V : VAS ι}

/-- The encoding of a finitely generated periodic set is finitely generated. -/
theorem relVecSet_closure (gens : Finset (VASConfig ι × VASConfig ι)) :
    ∃ s : Finset (ι ⊕ ι → ℤ), relVecSet (AddSubmonoid.closure
      (gens : Set (VASConfig ι × VASConfig ι)) : Set (VASConfig ι × VASConfig ι)) =
      (AddSubmonoid.closure (s : Set (ι ⊕ ι → ℤ)) : Set (ι ⊕ ι → ℤ)) := by
  classical
  refine ⟨gens.image relVecHom, ?_⟩
  rw [relVecSet, ← AddSubmonoid.coe_map, AddMonoidHom.map_mclosure, Finset.coe_image]

/-- The intersection of the reachability relation with a Presburger relation is almost
semilinear (Leroux, Section 6, before Lemma 6.2). -/
theorem almostSemilinear_reach_inter [Fintype ι] {R : Set (VASConfig ι × VASConfig ι)}
    (hR : IsSemilinearSet R) :
    AlmostSemilinear (relVecSet ({p | V.Reach p.1 p.2} ∩ R)) := by
  classical
  obtain ⟨F, hF, rfl⟩ := semilinear_decomp hR
  rw [Set.inter_iUnion₂, relVecSet, Set.image_iUnion₂]
  refine AlmostSemilinear.biUnion hF fun p _ => ?_
  obtain ⟨Min, hfin, -, heq⟩ := reach_inter_linear V p.1 p.2
  rw [heq, Set.image_iUnion₂]
  refine AlmostSemilinear.biUnion hfin fun π _ => ?_
  rw [Set.image_vadd_distrib, Set.image_inter relVecHom_injective, ← relVecSet, ← relVecSet]
  obtain ⟨s, hs⟩ := relVecSet_closure p.2
  rw [hs]
  obtain ⟨hP, hd⟩ := AsympDefinable.inter (runTrans_asympDefinable π).1 (isPeriodic_closure _)
    (runTrans_asympDefinable π).2 (asympDefinable_of_fg s)
  exact AlmostSemilinear.vadd_periodic _ hP hd

/-- **Theorem 9.1** (POPL): the reachability relation of a VAS is almost semilinear, i.e. its
intersection with every Presburger relation is. -/
theorem reach_isAlmostSemilinear [Fintype ι] :
    IsAlmostSemilinear (relVecSet {p : VASConfig ι × VASConfig ι | V.Reach p.1 p.2}) := by
  intro S hS
  have := almostSemilinear_reach_inter (V := V) (hS.preimage relVecHom)
  rw [relVecSet, Set.image_inter_preimage] at this
  exact this

/-- The encoding of a set of configurations in `ℤ^ι`. -/
def toIntSet (X : Set (VASConfig ι)) : Set (ι → ℤ) := VASConfig.toInt '' X

/-- **Corollary 6.3** (Leroux): `post(X) ∩ Y` and `pre(Y) ∩ X` are almost semilinear for
Presburger `X` and `Y`. -/
theorem almostSemilinear_post_inter [Fintype ι] {X Y : Set (VASConfig ι)}
    (hX : IsSemilinearSet X) (hY : IsSemilinearSet Y) :
    AlmostSemilinear (toIntSet (V.post X ∩ Y)) ∧ AlmostSemilinear (toIntSet (V.pre Y ∩ X)) := by
  have hE := almostSemilinear_reach_inter (V := V) (isSemilinearSet_prod hX hY)
  constructor
  · convert hE.image projR fun P hP => hP.projR using 1
    ext z
    constructor
    · rintro ⟨c, ⟨⟨x, hx, hxc⟩, hc⟩, rfl⟩
      exact ⟨_, ⟨(x, c), ⟨hxc, hx, hc⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨x, c⟩, ⟨hxc, hx, hc⟩, rfl⟩, rfl⟩
      exact ⟨c, ⟨⟨x, hx, hxc⟩, hc⟩, rfl⟩
  · convert hE.image projL fun P hP => hP.projL using 1
    ext z
    constructor
    · rintro ⟨c, ⟨⟨y, hy, hcy⟩, hc⟩, rfl⟩
      exact ⟨_, ⟨(c, y), ⟨hcy, hc, hy⟩, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨⟨c, y⟩, ⟨hcy, hc, hy⟩, rfl⟩, rfl⟩
      exact ⟨c, ⟨⟨y, hy, hcy⟩, hc⟩, rfl⟩

end Reach

end VAS

end Cslib
