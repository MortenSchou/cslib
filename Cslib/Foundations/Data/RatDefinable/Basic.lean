/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.BigOperators.Fin
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
public import Mathlib.Algebra.Order.Field.Rat

/-!
# Rationally definable sets

A set `C ⊆ ℚ^κ` is `RatDefinable` if it is a finite union of finite conjunctions of homogeneous
linear constraints `∑ i, a i * x i ≥ 0` or `> 0` with integer coefficients `a`. This is the
disjunctive normal form of the quantifier-free formulas of the first-order theory of `(ℚ; +, ≤, 0)`
(with integer scalars). The closure under projection, which is quantifier elimination for this
theory, is proved in `Cslib.Foundations.Data.RatDefinable.FourierMotzkin`.

## Main definitions

* `StrictRel`: the relation `0 < x` or `0 ≤ x`, chosen by a Boolean.
* `LinCons`: a homogeneous linear constraint, with `LinCons.eval` and `LinCons.Holds`.
* `RatDefinable`: finite unions of finite conjunctions of constraints.

## Main results

* `RatDefinable.inter`, `RatDefinable.union`, `RatDefinable.empty`, `RatDefinable.univ`,
  `RatDefinable.iUnion_list`.
* `RatDefinable.preimage`: preimage under an integer linear substitution of coordinates.
* `RatDefinable.comap`: preimage under a reindexing of coordinates.
* `RatDefinable.forall_fintype`: finite intersections of definable families.
* `RatDefinable.zero`, `RatDefinable.coord_nonneg`, `RatDefinable.coord_pos`,
  `RatDefinable.coord_pos_iff`: the sets cut out by one linear form or one coordinate.
-/

@[expose] public section

namespace Cslib

/-- `StrictRel σ x` is `0 < x` if `σ` (strict) and `0 ≤ x` otherwise. -/
def StrictRel (σ : Bool) (x : ℚ) : Prop := if σ then 0 < x else 0 ≤ x

namespace StrictRel

theorem of_pos {σ : Bool} {x : ℚ} (h : 0 < x) : StrictRel σ x := by
  cases σ <;> grind [StrictRel]

theorem nonneg {σ : Bool} {x : ℚ} (h : StrictRel σ x) : 0 ≤ x := by
  cases σ <;> grind [StrictRel]

theorem mono {σ : Bool} {x y : ℚ} (hxy : x ≤ y) (h : StrictRel σ x) : StrictRel σ y := by
  cases σ <;> grind [StrictRel]

theorem mul_pos {σ : Bool} {x c : ℚ} (hc : 0 < c) (h : StrictRel σ x) : StrictRel σ (c * x) := by
  cases σ
  · exact _root_.mul_nonneg hc.le h
  · exact _root_.mul_pos hc h

theorem add {σ τ : Bool} {x y : ℚ} (hx : StrictRel σ x) (hy : StrictRel τ y) :
    StrictRel (σ || τ) (x + y) := by
  cases σ <;> cases τ <;> grind [StrictRel]

theorem left {σ τ : Bool} {x : ℚ} (h : StrictRel (σ || τ) x) : StrictRel σ x := by
  cases σ <;> cases τ <;> grind [StrictRel]

theorem right {σ τ : Bool} {x : ℚ} (h : StrictRel (σ || τ) x) : StrictRel τ x := by
  cases σ <;> cases τ <;> grind [StrictRel]

end StrictRel

/-- A homogeneous linear constraint `∑ i, coeff i * x i ≥ 0` (or `> 0` when `strict`). -/
structure LinCons (κ : Type*) where
  /-- integer coefficients -/
  coeff : κ → ℤ
  /-- strict inequality? -/
  strict : Bool

variable {κ : Type*} [Fintype κ]

/-- The linear form `∑ i, coeff i * v i` of a constraint at a rational vector. -/
def LinCons.eval (g : LinCons κ) (v : κ → ℚ) : ℚ := ∑ i, (g.coeff i : ℚ) * v i

/-- The constraint holds at a rational vector. -/
def LinCons.Holds (g : LinCons κ) (v : κ → ℚ) : Prop := StrictRel g.strict (g.eval v)

/-- `C ⊆ ℚ^κ` is definable in `FO(ℚ; +, ≤, 0)`, concretely: a finite union of finite
conjunctions of homogeneous integer-coefficient inequalities. -/
def RatDefinable (C : Set (κ → ℚ)) : Prop :=
  ∃ S : List (List (LinCons κ)), C = {v | ∃ s ∈ S, ∀ g ∈ s, g.Holds v}

theorem LinCons.holds_of_strict {g : LinCons κ} {v : κ → ℚ} (h : g.strict = true) :
    g.Holds v ↔ 0 < ∑ i, (g.coeff i : ℚ) * v i := by
  simp [Holds, StrictRel, eval, h]

theorem LinCons.holds_of_not_strict {g : LinCons κ} {v : κ → ℚ} (h : g.strict = false) :
    g.Holds v ↔ 0 ≤ ∑ i, (g.coeff i : ℚ) * v i := by
  simp [Holds, StrictRel, eval, h]

/-- A set given by a list of systems of constraints is definable. -/
theorem ratDefinable_of_systems (S : List (List (LinCons κ))) :
    RatDefinable {v : κ → ℚ | ∃ s ∈ S, ∀ g ∈ s, g.Holds v} :=
  ⟨S, rfl⟩

namespace RatDefinable

/-- The empty set is definable. -/
theorem empty : RatDefinable (∅ : Set (κ → ℚ)) := ⟨[], by ext; simp⟩

/-- The whole space is definable. -/
theorem univ : RatDefinable (Set.univ : Set (κ → ℚ)) := ⟨[[]], by ext; simp⟩

/-- Closure of `RatDefinable` under union (concatenate the lists of systems). -/
theorem union {C D : Set (κ → ℚ)} (hC : RatDefinable C) (hD : RatDefinable D) :
    RatDefinable (C ∪ D) := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  refine ⟨S ++ T, ?_⟩
  ext v
  simp only [Set.mem_union, Set.mem_ofPred_eq, List.mem_append]
  grind

/-- Closure of `RatDefinable` under intersection (pairwise concatenation of systems). -/
theorem inter {C D : Set (κ → ℚ)} (hC : RatDefinable C) (hD : RatDefinable D) :
    RatDefinable (C ∩ D) := by
  obtain ⟨S, rfl⟩ := hC
  obtain ⟨T, rfl⟩ := hD
  refine ⟨S.flatMap fun s => T.map (s ++ ·), ?_⟩
  ext v
  simp only [Set.mem_inter_iff, Set.mem_ofPred_eq, List.mem_flatMap, List.mem_map]
  grind

/-- A finite union of definable sets is definable. -/
theorem iUnion_list {ι : Type*} (l : List ι) (C : ι → Set (κ → ℚ))
    (h : ∀ i ∈ l, RatDefinable (C i)) : RatDefinable {v | ∃ i ∈ l, v ∈ C i} := by
  induction l with
  | nil => simpa using empty
  | cons a l ih =>
    simpa [Set.ofPred_or] using (h a (by simp)).union (ih fun i hi => h i (by simp [hi]))

/-- Closure under preimage by an integer substitution of coordinates: `w ↦ (∑ j, f j i * w j)ᵢ`. -/
theorem preimage {κ' : Type*} [Fintype κ'] (f : κ' → κ → ℤ) {C : Set (κ → ℚ)}
    (hC : RatDefinable C) :
    RatDefinable {w : κ' → ℚ | (fun i => ∑ j, (f j i : ℚ) * w j) ∈ C} := by
  obtain ⟨S, rfl⟩ := hC
  let sub (g : LinCons κ) : LinCons κ' := ⟨fun j => ∑ i, g.coeff i * f j i, g.strict⟩
  have key (g : LinCons κ) (w : κ' → ℚ) :
      (sub g).Holds w ↔ g.Holds (fun i => ∑ j, (f j i : ℚ) * w j) := by
    suffices (sub g).eval w = g.eval (fun i => ∑ j, (f j i : ℚ) * w j) by
      simp only [LinCons.Holds, this, sub]
    simp only [LinCons.eval, sub, Int.cast_sum, Int.cast_mul, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    simp only [mul_assoc]
  refine ⟨S.map (·.map sub), ?_⟩
  ext w
  simp [key]

/-- Closure under reindexing of coordinates: `w ↦ w ∘ e`. -/
theorem comap {κ' : Type*} [Fintype κ'] (e : κ → κ') {C : Set (κ → ℚ)}
    (hC : RatDefinable C) : RatDefinable {w : κ' → ℚ | (fun i => w (e i)) ∈ C} := by
  classical
  convert hC.preimage (fun j i => if j = e i then (1 : ℤ) else 0) using 2
  simp

/-- A finite intersection of definable sets is definable. -/
theorem forall_fintype {J : Type*} [Finite J] {P : J → (κ → ℚ) → Prop}
    (h : ∀ j, RatDefinable {v | P j v}) : RatDefinable {v | ∀ j, P j v} := by
  classical
  have := Fintype.ofFinite J
  have key : ∀ s : Finset J, RatDefinable {v | ∀ j ∈ s, P j v} := fun s => by
    induction s using Finset.induction_on with
    | empty => simpa using (univ : RatDefinable (Set.univ : Set (κ → ℚ)))
    | insert a s _ ih => simpa [Set.ofPred_and] using (h a).inter ih
  simpa using key Finset.univ

/-- The set where a linear form with integer coefficients is zero is definable. -/
theorem zero (a : κ → ℤ) : RatDefinable {v : κ → ℚ | ∑ j, (a j : ℚ) * v j = 0} := by
  have := ratDefinable_of_systems [[(⟨a, false⟩ : LinCons κ), ⟨-a, false⟩]]
  convert this using 1
  ext v
  have hh (c : κ → ℤ) : (⟨c, false⟩ : LinCons κ).Holds v ↔ 0 ≤ ∑ j, (c j : ℚ) * v j :=
    LinCons.holds_of_not_strict rfl
  simp [hh, le_antisymm_iff, and_comm]

/-- The set where a coordinate is non-negative is definable. -/
theorem coord_nonneg (j : κ) : RatDefinable {v : κ → ℚ | 0 ≤ v j} := by
  classical
  convert ratDefinable_of_systems [[(⟨Pi.single j 1, false⟩ : LinCons κ)]] using 1
  ext v
  simp [LinCons.Holds, LinCons.eval, StrictRel, Pi.single_apply]

/-- The set where a coordinate is positive is definable. -/
theorem coord_pos (j : κ) : RatDefinable {v : κ → ℚ | 0 < v j} := by
  classical
  convert ratDefinable_of_systems [[(⟨Pi.single j 1, true⟩ : LinCons κ)]] using 1
  ext v
  simp [LinCons.Holds, LinCons.eval, StrictRel, Pi.single_apply]

/-- The set where a coordinate is positive iff a fixed proposition holds is definable. -/
theorem coord_pos_iff (j : κ) (P : Prop) : RatDefinable {v : κ → ℚ | 0 < v j ↔ P} := by
  classical
  by_cases hP : P
  · simpa [hP] using coord_pos j
  · convert ratDefinable_of_systems [[(⟨Pi.single j (-1), false⟩ : LinCons κ)]] using 1
    ext v
    simp [hP, LinCons.Holds, LinCons.eval, StrictRel, Pi.single_apply]

end RatDefinable

end Cslib
