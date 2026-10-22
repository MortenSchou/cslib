/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Defs
public import Cslib.Init

/-! # Effective representations of vector addition systems and semilinear sets

Finite objects (lists of numbers) that denote vector addition systems and semilinear sets, so that
the existence of a Presburger inductive invariant can be searched for by a program. Lists are read
as vectors with missing entries `0`, so that every list is a code and no length invariant has to be
carried around.

## Main definitions

- `vecN`, `vecZ`: read a list as a vector in `Fin d → ℕ`, `Fin d → ℤ`; missing entries are `0`.
- `SLCode`: a code for a semilinear set, a finite list of pairs (base, periods).
- `SLCode.set`: the semilinear set denoted by a code.
- `VASCode`, `VASCode.toVAS`: a code for a VAS, its dimension and a list of actions.
- `VASCode.Certificate`: a coded semilinear inductive set that contains `x` and omits `y`.

## Main statements

- `isSemilinearSet_iff_exists_code`: the semilinear sets are exactly the sets denoted by codes.
-/

@[expose] public section

namespace Cslib

open Set Pointwise AddSubmonoid

/-- Read a list of natural numbers as a vector in dimension `d`; missing entries are `0`. -/
def vecN (d : ℕ) (l : List ℕ) : Fin d → ℕ := fun i => l.getD i 0

/-- Read a list of integers as a vector in dimension `d`; missing entries are `0`. -/
def vecZ (d : ℕ) (l : List ℤ) : Fin d → ℤ := fun i => l.getD i 0

@[simp] theorem vecN_ofFn {d : ℕ} (v : Fin d → ℕ) : vecN d (List.ofFn v) = v := by
  funext i
  simp [vecN, List.getD_eq_getElem?_getD]

/-- A code for a semilinear set: a finite list of pairs `(base, periods)`, one for each linear
set of the union. -/
abbrev SLCode := List (List ℕ × List (List ℕ))

/-- The linear set `base + ℕ p₁ + ⋯ + ℕ p_k` coded by `(base, [p₁, …, p_k])`. -/
def linSet (d : ℕ) (l : List ℕ × List (List ℕ)) : Set (Fin d → ℕ) :=
  vecN d l.1 +ᵥ (closure {y | y ∈ l.2.map (vecN d)} : Set (Fin d → ℕ))

/-- The semilinear set denoted by a code. -/
def SLCode.set (d : ℕ) (r : SLCode) : Set (Fin d → ℕ) := ⋃ l ∈ r, linSet d l

/-- A code of a VAS: the dimension and the list of actions. -/
abbrev VASCode := ℕ × List (List ℤ)

/-- The VAS denoted by a code. -/
def VASCode.toVAS (c : VASCode) : VAS (Fin c.1) where
  acts := (c.2.map (vecZ c.1)).toFinset

theorem VASCode.mem_acts {c : VASCode} {a : Fin c.1 → ℤ} :
    a ∈ c.toVAS.acts ↔ ∃ l ∈ c.2, vecZ c.1 l = a := by
  simp [VASCode.toVAS]

/-- The certificate that `y` is not reachable from `x`: `r` codes a semilinear inductive set that
contains `x` and omits `y`. -/
def VASCode.Certificate (c : VASCode) (x y : List ℕ) (r : SLCode) : Prop :=
  c.toVAS.IsInductive (r.set c.1) ∧ vecN c.1 x ∈ r.set c.1 ∧ vecN c.1 y ∉ r.set c.1

@[simp] theorem SLCode.set_append (d : ℕ) (r₁ r₂ : SLCode) :
    (r₁ ++ r₂).set d = r₁.set d ∪ r₂.set d := by
  simp [SLCode.set, Set.iUnion_or, Set.iUnion_union_distrib]

theorem mem_closure_list {M : Type*} [AddCommMonoid M] (L : List M) (x : M) :
    x ∈ closure {y | y ∈ L} ↔
      ∃ ns : List ℕ, ns.length = L.length ∧ x = (List.zipWith (fun n p => n • p) ns L).sum := by
  induction L generalizing x with
  | nil => simp
  | cons p L ih =>
    rw [show {y | y ∈ p :: L} = {p} ∪ {y | y ∈ L} by ext; simp, closure_union, mem_sup]
    simp only [mem_closure_singleton, ih, List.length_cons]
    constructor
    · rintro ⟨_, ⟨n, rfl⟩, z, ⟨ns, hns, rfl⟩, rfl⟩
      exact ⟨n :: ns, by simp [hns], by simp⟩
    · rintro ⟨_ | ⟨n, ns⟩, hns, rfl⟩
      · simp at hns
      · exact ⟨_, ⟨n, rfl⟩, _, ⟨ns, by simpa using hns, rfl⟩, by simp⟩

theorem mem_linSet {d : ℕ} {l : List ℕ × List (List ℕ)} {v : Fin d → ℕ} :
    v ∈ linSet d l ↔ ∃ ns : List ℕ, ns.length = l.2.length ∧
      v = vecN d l.1 + (List.zipWith (fun n p => n • vecN d p) ns l.2).sum := by
  simp only [linSet, mem_vadd_set, SetLike.mem_coe, mem_closure_list, vadd_eq_add,
    List.length_map, List.zipWith_map_right]
  constructor
  · rintro ⟨_, ⟨ns, hns, rfl⟩, rfl⟩
    exact ⟨ns, hns, by rw [add_comm]⟩
  · rintro ⟨ns, hns, rfl⟩
    exact ⟨_, ⟨ns, hns, rfl⟩, by rw [add_comm]⟩

theorem isLinearSet_linSet (d : ℕ) (l : List ℕ × List (List ℕ)) : IsLinearSet (linSet d l) :=
  ⟨_, _, List.finite_toSet _, rfl⟩

theorem exists_code_of_isLinearSet {d : ℕ} {s : Set (Fin d → ℕ)} (hs : IsLinearSet s) :
    ∃ r : SLCode, r.set d = s := by
  obtain ⟨a, u, rfl⟩ := isLinearSet_iff.1 hs
  refine ⟨[(List.ofFn a, u.toList.map List.ofFn)], ?_⟩
  simp [SLCode.set, linSet]

/-- Semilinear sets (Mathlib) are exactly the sets denoted by codes. -/
theorem isSemilinearSet_iff_exists_code {d : ℕ} {s : Set (Fin d → ℕ)} :
    IsSemilinearSet s ↔ ∃ r : SLCode, r.set d = s := by
  refine ⟨fun hs => ?_, ?_⟩
  · obtain ⟨S, hS, rfl⟩ := isSemilinearSet_iff.1 hs
    clear hs
    induction S using Finset.induction_on with
    | empty => exact ⟨[], by simp [SLCode.set]⟩
    | insert t S _ ih =>
      obtain ⟨r₁, h₁⟩ := exists_code_of_isLinearSet (hS t (Finset.mem_insert_self _ _))
      obtain ⟨r₂, h₂⟩ := ih fun u hu => hS u (Finset.mem_insert_of_mem hu)
      exact ⟨r₁ ++ r₂, by simp [← h₁, ← h₂]⟩
  · rintro ⟨r, rfl⟩
    exact IsSemilinearSet.biUnion r.finite_toSet fun l _ => (isLinearSet_linSet d l).isSemilinearSet

end Cslib
