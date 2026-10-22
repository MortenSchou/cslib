/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Defs

/-! # Vector addition systems: basic lemmas

Monotony of reachability, the characterisation of `post` and `pre` as least invariants, and the
elementary facts about inductive invariants and separators.

## Main statements

- `VAS.Reach.add_left`: monotony, runs can be translated by any configuration.
- `VAS.isInductive_post`, `VAS.isBackInductive_pre`: `post` and `pre` are invariants.
- `VAS.IsInductive.reach_mem`, `VAS.IsBackInductive.reach_mem`: soundness of invariants.
- `VAS.Separator.inductive_of_domain_empty`: a separator with empty domain is a partition into a
  forward and a backward invariant.
- `VAS.not_reach_of_isInductive`: the easy half of the invariant criterion for non-reachability.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

namespace VAS

variable {ι : Type*} (V : VAS ι)

/-- The integer view is additive. -/
@[simp] theorem _root_.Cslib.VASConfig.toInt_add (c d : VASConfig ι) :
    (c + d).toInt = c.toInt + d.toInt := by
  funext i
  simp [VASConfig.toInt]

/-- The integer view is compatible with multiples. -/
theorem _root_.Cslib.VASConfig.toInt_nsmul (n : ℕ) (c : VASConfig ι) :
    (n • c).toInt = n • c.toInt := by
  funext i
  simp [VASConfig.toInt]

variable {V} in
/-- Monotony: a move can be translated by any configuration. -/
theorem Move.add_left {x y : VASConfig ι} (h : V.Move x y) (c : VASConfig ι) :
    V.Move (c + x) (c + y) := by
  obtain ⟨a, ha, hxy⟩ := h
  exact ⟨a, ha, by rw [VASConfig.toInt_add, VASConfig.toInt_add, hxy, add_assoc]⟩

variable {V} in
/-- Monotony (Leroux, Lemma 3.1): runs can be translated by any configuration. -/
theorem Reach.add_left {x y : VASConfig ι} (h : V.Reach x y) (c : VASConfig ι) :
    V.Reach (c + x) (c + y) :=
  LTS.CanReach.lift (lts := V.lts) (lts' := V.lts) (c + ·) (fun _ _ hm => Move.add_left hm c) h

/-- `post X` is a forward inductive invariant. -/
theorem isInductive_post (X : Set (VASConfig ι)) : V.IsInductive (V.post X) :=
  fun _ ⟨x, hx, hxc⟩ _ hc => ⟨x, hx, hxc.tail hc⟩

/-- `pre Y` is a backward inductive invariant. -/
theorem isBackInductive_pre (Y : Set (VASConfig ι)) : V.IsBackInductive (V.pre Y) :=
  fun _ ⟨y, hy, hc'y⟩ _ hc => ⟨y, hy, .head hc hc'y⟩

/-- `X` is contained in `post X`. -/
theorem subset_post (X : Set (VASConfig ι)) : X ⊆ V.post X :=
  fun x hx => ⟨x, hx, .refl⟩

/-- `Y` is contained in `pre Y`. -/
theorem subset_pre (Y : Set (VASConfig ι)) : Y ⊆ V.pre Y :=
  fun y hy => ⟨y, hy, .refl⟩

/-- `post X` is the least forward inductive invariant containing `X`. -/
theorem post_subset_of_isInductive {X Z : Set (VASConfig ι)} (hZ : V.IsInductive Z)
    (hXZ : X ⊆ Z) : V.post X ⊆ Z := by
  rintro y ⟨x, hx, hxy⟩
  induction hxy using LTS.CanReach.induction_on with
  | refl => exact hXZ hx
  | tail _ hm ih => exact hZ _ ih _ hm

/-- `pre Y` is the least backward inductive invariant containing `Y`. -/
theorem pre_subset_of_isBackInductive {Y Z : Set (VASConfig ι)} (hZ : V.IsBackInductive Z)
    (hYZ : Y ⊆ Z) : V.pre Y ⊆ Z := by
  rintro x ⟨y, hy, hxy⟩
  induction hxy using LTS.CanReach.head_induction_on with
  | refl => exact hYZ hy
  | head hm _ ih => exact hZ _ ih _ hm

variable {V}

/-- Soundness of forward invariants: an inductive set containing `x` contains everything
reachable from `x`. -/
theorem IsInductive.reach_mem {X : Set (VASConfig ι)} (hX : V.IsInductive X) {x y : VASConfig ι}
    (hx : x ∈ X) (h : V.Reach x y) : y ∈ X :=
  V.post_subset_of_isInductive hX (fun _ h => h) ⟨x, hx, h⟩

/-- Soundness of backward invariants. -/
theorem IsBackInductive.reach_mem {Y : Set (VASConfig ι)} (hY : V.IsBackInductive Y)
    {x y : VASConfig ι} (hy : y ∈ Y) (h : V.Reach x y) : x ∈ Y :=
  V.pre_subset_of_isBackInductive hY (fun _ h => h) ⟨y, hy, h⟩

/-- The easy half of the invariant criterion: an inductive invariant containing `x` and not `y`
shows that `y` is not reachable from `x`. -/
theorem not_reach_of_isInductive {X : Set (VASConfig ι)} (hX : V.IsInductive X) {x y : VASConfig ι}
    (hx : x ∈ X) (hy : y ∉ X) : ¬ V.Reach x y :=
  fun h => hy (hX.reach_mem hx h)

end VAS

/-- A separator with empty domain is a partition into a forward invariant `X` and a backward
invariant `Y`. -/
theorem VAS.Separator.inductive_of_domain_empty {ι : Type*} {V : VAS ι} {X Y : Set (VASConfig ι)}
    (h : V.Separator X Y) (hD : VAS.domain X Y = ∅) :
    V.IsInductive X ∧ V.IsBackInductive Y ∧ Disjoint X Y := by
  have hcov (c) : c ∈ X ∨ c ∈ Y := by
    by_contra hc
    have : c ∈ VAS.domain X Y := by simpa [VAS.domain, not_or] using hc
    simp [hD] at this
  refine ⟨fun c hc c' hm => ?_, fun c' hc' c hm => ?_, Set.disjoint_left.2 fun x hx hy => ?_⟩
  · exact (hcov c').resolve_right fun hc' => h.no_run c hc c' hc' (.single hm)
  · exact (hcov c).resolve_left fun hc => h.no_run c hc c' hc' (.single hm)
  · exact h.no_run x hx x hy .refl

end Cslib
