/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Cslib.Foundations.Relation.FiniteClosure
public import Mathlib.Logic.Relation
public import Mathlib.Data.Set.Finite.Basic
public import Mathlib.Order.Interval.Finset.Nat
public import Mathlib.Data.Fintype.Pigeonhole

/-! # Fair paths in finite graphs

In a finite graph, an infinite path visiting each of finitely many sets infinitely often exists iff
a reachable cycle visits each set. This is the criterion behind LTL model checking: the existence
of a path satisfying a formula is the existence of a *fair* path in a product graph, where fairness
requires the eventualities of the formula to be fulfilled infinitely often.

## Main definitions

- `FairPath`: an infinite path visiting each given set infinitely often.
- `FairCycleFrom`: a state reachable from `x` with a cycle through all the given sets.

## Main statements

- `fairPath_iff_fairCycleFrom`: for finite graphs, the two agree.
-/

@[expose] public section

namespace Cslib.Logic.LTL

variable {V : Type*} {ι : Type*} (R : V → V → Prop) (P : ι → V → Prop)

/-- An infinite path from `x` visiting each given set infinitely often. -/
def FairPath (F : List ι) (x : V) : Prop :=
  ∃ g : ℕ → V, g 0 = x ∧ (∀ n, R (g n) (g (n + 1))) ∧ ∀ i ∈ F, ∀ n, ∃ m ≥ n, P i (g m)

/-- A walk from `y` through the given sets in order, ending at `z`. -/
def Visits : V → List ι → V → Prop
  | y, [], z => Relation.ReflTransGen R y z
  | y, i :: is, z => ∃ a, Relation.ReflTransGen R y a ∧ P i a ∧ Visits a is z

/-- A state reachable from `x` that lies on a cycle visiting each given set. -/
def FairCycleFrom (F : List ι) (x : V) : Prop :=
  ∃ y, Relation.ReflTransGen R x y ∧ ∃ y', R y y' ∧ Visits R P y' F y

/-- A walk of length `n` from `a` to `b`, as a sequence. -/
def IsWalk (a b : V) (n : ℕ) (w : ℕ → V) : Prop :=
  w 0 = a ∧ w n = b ∧ ∀ i < n, R (w i) (w (i + 1))

variable {R} {P}

theorem exists_walk {a b : V} (h : Relation.ReflTransGen R a b) : ∃ n w, IsWalk R a b n w := by
  induction h with
  | refl => exact ⟨0, fun _ => a, rfl, rfl, fun i hi => absurd hi (Nat.not_lt_zero i)⟩
  | @tail b c _ hbc ih =>
    obtain ⟨n, w, h0, hn, hs⟩ := ih
    refine ⟨n + 1, fun i => if i ≤ n then w i else c, by simp [h0], by simp, fun i hi => ?_⟩
    by_cases hin : i + 1 ≤ n
    · simp only [show i ≤ n by omega, hin, ite_true]
      exact hs i (by omega)
    · have : i = n := by omega
      subst this
      change R (if i ≤ i then w i else c) (if i + 1 ≤ i then w (i + 1) else c)
      simp only [le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false, hn]
      exact hbc

/-- Concatenation of two walks. -/
def cat (n₁ : ℕ) (w₁ w₂ : ℕ → V) : ℕ → V := fun i => if i ≤ n₁ then w₁ i else w₂ (i - n₁)

theorem IsWalk.append {a b c : V} {n₁ n₂ : ℕ} {w₁ w₂ : ℕ → V} (h₁ : IsWalk R a b n₁ w₁)
    (h₂ : IsWalk R b c n₂ w₂) : IsWalk R a c (n₁ + n₂) (cat n₁ w₁ w₂) := by
  obtain ⟨h10, h1n, h1s⟩ := h₁
  obtain ⟨h20, h2n, h2s⟩ := h₂
  refine ⟨by simp [cat, h10], ?_, fun i hi => ?_⟩
  · by_cases hn : n₂ = 0
    · subst hn
      simp [cat, h1n, ← h20, h2n]
    · simp only [cat, show ¬ (n₁ + n₂ ≤ n₁) by omega, ite_false]
      simpa using h2n
  · by_cases hi1 : i + 1 ≤ n₁
    · simp only [cat, show i ≤ n₁ by omega, hi1, ite_true]
      exact h1s i (by omega)
    · by_cases hi0 : i ≤ n₁
      · have : i = n₁ := by omega
        subst this
        have h2 := h2s 0 (by omega)
        simp only [cat, le_refl, ite_true, show ¬ (i + 1 ≤ i) by omega, ite_false, h1n]
        rw [← h20]
        simpa using h2
      · have h2 := h2s (i - n₁) (by omega)
        simp only [cat, hi0, hi1, ite_false]
        rw [show i + 1 - n₁ = i - n₁ + 1 by omega]
        exact h2

theorem cat_add {n₁ : ℕ} {w₁ w₂ : ℕ → V} (h : w₁ n₁ = w₂ 0) (j : ℕ) :
    cat n₁ w₁ w₂ (n₁ + j) = w₂ j := by
  by_cases hj : j = 0
  · subst hj; simp [cat, h]
  · simp [cat, show ¬ (n₁ + j ≤ n₁) by omega]

/-- A walk visiting all sets of `is` in order yields a walk with a visit to each. -/
theorem Visits.exists_walk {y z : V} : ∀ {is : List ι}, Visits R P y is z →
    ∃ n w, IsWalk R y z n w ∧ ∀ i ∈ is, ∃ j ≤ n, P i (w j)
  | [], h => by
    obtain ⟨n, w, hw⟩ := _root_.Cslib.Logic.LTL.exists_walk h
    exact ⟨n, w, hw, fun i hi => absurd hi (List.not_mem_nil)⟩
  | i₀ :: is, ⟨a, hya, hPa, hrest⟩ => by
    obtain ⟨n₁, w₁, hw₁⟩ := _root_.Cslib.Logic.LTL.exists_walk hya
    obtain ⟨n₂, w₂, hw₂, hmarks⟩ := Visits.exists_walk hrest
    refine ⟨n₁ + n₂, cat n₁ w₁ w₂, hw₁.append hw₂, fun i hi => ?_⟩
    rcases List.mem_cons.1 hi with rfl | hi'
    · exact ⟨n₁, by omega, by simpa [cat, hw₁.2.1] using hPa⟩
    · obtain ⟨j, hj, hQj⟩ := hmarks i hi'
      exact ⟨n₁ + j, by omega, by rwa [cat_add (hw₁.2.1.trans hw₂.1.symm)]⟩

/-- A closed walk of positive length visiting each set gives a fair path. -/
theorem fairPath_of_closedWalk {F : List ι} {y : V} {n : ℕ} {w : ℕ → V} (hn : 0 < n)
    (hw : IsWalk R y y n w) (hmarks : ∀ i ∈ F, ∃ j ≤ n, P i (w j)) : FairPath R P F y := by
  obtain ⟨h0, hnn, hs⟩ := hw
  have hmod : ∀ j ≤ n, w (j % n) = w j := fun j hj => by
    rcases lt_or_eq_of_le hj with hlt | rfl
    · rw [Nat.mod_eq_of_lt hlt]
    · rw [Nat.mod_self, h0, hnn]
  refine ⟨fun i => w (i % n), by simp [h0], fun i => ?_, fun k hk N => ?_⟩
  · have hr : i % n < n := Nat.mod_lt _ hn
    have hsucc : (i + 1) % n = (i % n + 1) % n := (Nat.mod_add_mod i n 1).symm
    change R (w (i % n)) (w ((i + 1) % n))
    by_cases hlt : i % n + 1 < n
    · rw [hsucc, Nat.mod_eq_of_lt hlt]
      exact hs _ hr
    · have hfin : i % n + 1 = n := by omega
      have hstep := hs _ hr
      rw [hfin, hnn] at hstep
      rw [hsucc, hfin, Nat.mod_self, h0]
      exact hstep
  · obtain ⟨j, hj, hPj⟩ := hmarks k hk
    refine ⟨(N + 1) * n + j % n, ?_, ?_⟩
    · have : N + 1 ≤ (N + 1) * n := Nat.le_mul_of_pos_right _ hn
      omega
    · change P k (w (((N + 1) * n + j % n) % n))
      rw [Nat.mul_comm (N + 1) n, Nat.mul_add_mod, Nat.mod_mod, hmod j hj]
      exact hPj

/-- A fair path from the successor of a state is a fair path from the state. -/
theorem FairPath.cons {F : List ι} {x x' : V} (h : FairPath R P F x') (hx : R x x') :
    FairPath R P F x := by
  obtain ⟨g, h0, hs, hf⟩ := h
  refine ⟨fun n => Nat.casesOn n x g, rfl, fun n => ?_, fun k hk n => ?_⟩
  · cases n with
    | zero => simpa [h0] using hx
    | succ n => exact hs n
  · cases n with
    | zero =>
      obtain ⟨m, _, hm⟩ := hf k hk 0
      exact ⟨m + 1, Nat.zero_le _, hm⟩
    | succ n =>
      obtain ⟨m, hm, hPm⟩ := hf k hk n
      exact ⟨m + 1, by omega, hPm⟩

/-- Later states of a path are reachable. -/
theorem reach_of_path {g : ℕ → V} (hs : ∀ n, R (g n) (g (n + 1))) {i j : ℕ} (h : i ≤ j) :
    Relation.ReflTransGen R (g i) (g j) := by
  induction j, h using Nat.le_induction with
  | base => exact .refl
  | succ j _ ih => exact ih.tail (hs j)

theorem Visits.extend {z z' : V} (h : Relation.ReflTransGen R z z') :
    ∀ {is : List ι} {y : V}, Visits R P y is z → Visits R P y is z'
  | [], _, hv => hv.trans h
  | _ :: _, _, ⟨a, hya, hPa, hrest⟩ => ⟨a, hya, hPa, Visits.extend h hrest⟩

/-- A cycle visiting each set yields a fair path. -/
theorem fairPath_of_fairCycleFrom {F : List ι} {x : V} (h : FairCycleFrom R P F x) :
    FairPath R P F x := by
  obtain ⟨y, hxy, y', hyy', hv⟩ := h
  have hy : FairPath R P F y := by
    obtain ⟨n₂, w₂, hw₂, hmarks⟩ := hv.exists_walk
    let w₁ : ℕ → V := fun i => if i = 0 then y else y'
    have hw₁ : IsWalk R y y' 1 w₁ :=
      ⟨by simp [w₁], by simp [w₁], fun i hi => by
        have : i = 0 := by omega
        subst this; simpa [w₁] using hyy'⟩
    have hjoin : w₁ 1 = w₂ 0 := by simp [w₁, hw₂.1]
    refine fairPath_of_closedWalk (n := 1 + n₂) (w := cat 1 w₁ w₂) (by omega)
      (hw₁.append hw₂) fun i hi => ?_
    obtain ⟨j, hj, hPj⟩ := hmarks i hi
    exact ⟨1 + j, by omega, by rwa [cat_add hjoin]⟩
  induction hxy using Relation.ReflTransGen.head_induction_on with
  | refl => exact hy
  | head hab _ ih => exact ih.cons hab

variable [Finite V]

/-- A fair path in a finite graph yields a reachable cycle through all the sets. -/
theorem fairCycleFrom_of_fairPath {F : List ι} {x : V} (h : FairPath R P F x) :
    FairCycleFrom R P F x := by
  obtain ⟨g, h0, hs, hf⟩ := h
  obtain ⟨y, hy⟩ := Finite.exists_infinite_fiber g
  have hinf : (g ⁻¹' {y}).Infinite := Set.infinite_coe_iff.1 hy
  have hvis : ∀ (is : List ι), (∀ i ∈ is, ∀ n, ∃ m ≥ n, P i (g m)) →
      ∀ i, ∃ j ≥ i, Visits R P (g i) is (g j) := by
    intro is
    induction is with
    | nil => exact fun _ i => ⟨i, le_rfl, .refl⟩
    | cons k is ih =>
      intro hPs i
      obtain ⟨m, hm, hPm⟩ := hPs k List.mem_cons_self i
      obtain ⟨j, hj, hv⟩ := ih (fun q hq => hPs q (List.mem_cons_of_mem _ hq)) m
      exact ⟨j, hm.trans hj, g m, reach_of_path hs hm, hPm, hv⟩
  obtain ⟨n₀, hn₀, -⟩ := Set.Infinite.exists_gt hinf 0
  have hgn₀ : g n₀ = y := hn₀
  obtain ⟨j, hj, hv⟩ := hvis F hf (n₀ + 1)
  obtain ⟨j', hj', hjj'⟩ := Set.Infinite.exists_gt hinf j
  refine ⟨g n₀, ?_, g (n₀ + 1), hs n₀, ?_⟩
  · rw [← h0]; exact reach_of_path hs (Nat.zero_le _)
  · rw [hgn₀]
    have : g j' = y := hj'
    rw [← this]
    exact hv.extend (reach_of_path hs hjj'.le)

/-- In a finite graph, a fair path exists iff a reachable cycle visits every set. -/
theorem fairPath_iff_fairCycleFrom {F : List ι} {x : V} :
    FairPath R P F x ↔ FairCycleFrom R P F x :=
  ⟨fairCycleFrom_of_fairPath, fairPath_of_fairCycleFrom⟩

section Decidable

variable [Fintype V] [DecidableEq V] [DecidableRel R] [∀ i v, Decidable (P i v)]

instance decidableVisits : ∀ (y : V) (is : List ι) (z : V), Decidable (Visits R P y is z)
  | y, [], z => inferInstanceAs (Decidable (Relation.ReflTransGen R y z))
  | y, i :: is, z =>
    have : ∀ a, Decidable (Visits R P a is z) := fun a => decidableVisits a is z
    inferInstanceAs (Decidable (∃ a, Relation.ReflTransGen R y a ∧ P i a ∧ Visits R P a is z))

instance (F : List ι) (x : V) : Decidable (FairCycleFrom R P F x) :=
  inferInstanceAs (Decidable (∃ y, Relation.ReflTransGen R x y ∧ ∃ y', R y y' ∧ Visits R P y' F y))

/-- The existence of a fair path in a finite graph is decidable. -/
instance (F : List ι) (x : V) : Decidable (FairPath R P F x) :=
  decidable_of_iff _ fairPath_iff_fairCycleFrom.symm

end Decidable

end Cslib.Logic.LTL
