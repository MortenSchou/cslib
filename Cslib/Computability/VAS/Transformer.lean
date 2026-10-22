/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.Run
public import Cslib.Computability.VAS.Periodic
public import Mathlib.Tactic.Abel
public import Mathlib.Data.Rat.Defs
public import Mathlib.Algebra.Order.BigOperators.Group.Finset
public import Mathlib.Data.Nat.Nth
public import Mathlib.Order.WellQuasiOrder

/-! # Transformer relations: triples and intraproductions

The transformer relation with capacity `c` of a VAS is `x ▷_c y` iff there is a run from `c + x`
to `c + y`. This file shows that it is periodic and develops the combinatorics of the *triples*
`γ = (x, c, y)` with `x ▷_c y` (Leroux, Section 5): the runs `Ω_γ`, the configurations `Q_γ` they
visit, the bounded components `I_γ` and the intraproductions `H_γ`.

## Main definitions

* `VAS.transSet`: the transformer relation `▷_c`, encoded as a set of vectors of `ℤ^(ι ⊕ ι)`.
* `VAS.Triple`: a triple `γ = (x, c, y)`, with `runs`, `Q`, `bounded` and `intraprod`.

## Main results

* `VAS.transSet_periodic`: `▷_c` is periodic.
* `VAS.Triple.Q_add_intraprod`: `Q_γ + H_γ ⊆ Q_γ`.
* `VAS.Triple.exists_intraprod_ge`: comparable configurations of `Q_γ` differ by an
  intraproduction.
* `VAS.Triple.exists_intraprod_support`: an intraproduction positive exactly on the unbounded
  components exists.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

variable {ι : Type*}

namespace VAS

section Reach

variable {V : VAS ι} {a a' b b' c : VASConfig ι}

/-- Rewriting the endpoints of a run. -/
theorem reach_cast {x y x' y' : VASConfig ι} (h : V.Reach x y) (hx : x = x') (hy : y = y') :
    V.Reach x' y' := hx ▸ hy ▸ h

/-- Runs with capacity `c` can be added. -/
theorem reach_add (h : V.Reach (c + a) (c + b)) (h' : V.Reach (c + a') (c + b')) :
    V.Reach (c + (a + a')) (c + (b + b')) := by
  have h1 : V.Reach (c + (a + a')) (a' + (c + b)) :=
    reach_cast (Reach.add_left h a') (by abel) rfl
  have h2 : V.Reach (a' + (c + b)) (c + (b + b')) :=
    reach_cast (Reach.add_left h' b) (by abel) (by abel)
  exact h1.trans h2

/-- Runs with capacity `c` can be iterated. -/
theorem reach_nsmul (h : V.Reach (c + a) (c + b)) (n : ℕ) :
    V.Reach (c + n • a) (c + n • b) := by
  induction n with
  | zero => simp only [zero_smul, add_zero]; exact Reach.refl
  | succ n ih =>
    simp only [succ_nsmul]
    exact reach_add ih h

end Reach

variable (V : VAS ι)

/-- The transformer relation with capacity `c`: `x ▷_c y` iff there is a run from `c + x` to
`c + y`, encoded as the set of vectors `(x, y) ∈ ℤ^(ι ⊕ ι)`. -/
def transSet (c : VASConfig ι) : Set (ι ⊕ ι → ℤ) :=
  {w | ∃ x y : VASConfig ι, relVec x y = w ∧ V.Reach (c + x) (c + y)}

/-- The encoding `(x, y) ↦ relVec x y` of pairs of configurations in `ℤ^(ι ⊕ ι)` as an additive
map. -/
def relVecHom : VASConfig ι × VASConfig ι →+ (ι ⊕ ι → ℤ) where
  toFun p := relVec p.1 p.2
  map_zero' := by ext (i | i) <;> simp [relVec, VASConfig.toInt]
  map_add' _ _ := by ext (i | i) <;> simp [relVec, VASConfig.toInt]

theorem relVecHom_injective : Function.Injective (relVecHom (ι := ι)) := by
  rintro ⟨x, y⟩ ⟨x', y'⟩ h
  have hx (i : ι) : (x i : ℤ) = x' i := congrFun h (Sum.inl i)
  have hy (i : ι) : (y i : ℤ) = y' i := congrFun h (Sum.inr i)
  ext i <;> simp [← Nat.cast_inj (R := ℤ), hx, hy]

/-- The transformer relation `▷_c` is periodic (Leroux, Lemma 5.2). -/
theorem transSet_periodic (c : VASConfig ι) : IsPeriodic (V.transSet c) := by
  refine ⟨⟨0, 0, map_zero relVecHom, ?_⟩, ?_⟩
  · exact Reach.refl
  · rintro _ ⟨x, y, rfl, h⟩ _ ⟨x', y', rfl, h'⟩
    exact ⟨x + x', y + y', map_add relVecHom (x, y) (x', y'), reach_add h h'⟩

/-- A *triple* `γ = (x, c, y)` with `x ▷_c y` (Leroux, Section 5). -/
structure Triple where
  /-- The source vector. -/
  x : VASConfig ι
  /-- The capacity. -/
  c : VASConfig ι
  /-- The target vector. -/
  y : VASConfig ι
  /-- The run witnessing `x ▷_c y`. -/
  mem : V.Reach (c + x) (c + y)

namespace Triple

variable {V}

/-- `Ω_γ`: the runs whose direction lies in `(c, c) + ℕ (x, y)`. -/
def runs (γ : Triple V) : Set V.Run :=
  {π | ∃ n : ℕ, π.src = γ.c + n • γ.x ∧ π.tgt = γ.c + n • γ.y}

/-- `Q_γ`: the configurations occurring in some run of `Ω_γ`. -/
def Q (γ : Triple V) : Set (VASConfig ι) := {q | ∃ π ∈ γ.runs, q ∈ π.cfgs}

/-- `I_γ`: the bounded components, those `i` for which `{q i | q ∈ Q_γ}` is finite. -/
def bounded (γ : Triple V) : Set ι := {i | ((fun q : VASConfig ι => q i) '' γ.Q).Finite}

/-- `H_γ`: the intraproductions, the `h` with `n x ▷_c h ▷_c n y` for some `n`. -/
def intraprod (γ : Triple V) : Set (VASConfig ι) :=
  {h | ∃ n : ℕ, V.Reach (γ.c + n • γ.x) (γ.c + h) ∧ V.Reach (γ.c + h) (γ.c + n • γ.y)}

variable (γ : Triple V)

/-- A configuration is in `Q_γ` iff it lies between `c + n x` and `c + n y` for some `n`. -/
theorem mem_Q_iff {q : VASConfig ι} :
    q ∈ γ.Q ↔ ∃ n : ℕ, V.Reach (γ.c + n • γ.x) q ∧ V.Reach q (γ.c + n • γ.y) := by
  constructor
  · rintro ⟨π, ⟨n, hs, ht⟩, hq⟩
    have := π.mem_reach hq
    exact ⟨n, hs ▸ this.1, ht ▸ this.2⟩
  · rintro ⟨n, h1, h2⟩
    obtain ⟨π, hs, ht, hq⟩ := Run.exists_run_through h1 h2
    exact ⟨π, ⟨n, hs, ht⟩, hq⟩

/-- The capacity belongs to `Q_γ`. -/
theorem c_mem_Q : γ.c ∈ γ.Q := by
  refine (mem_Q_iff γ).2 ⟨0, ?_, ?_⟩ <;>
    rw [zero_smul, add_zero]

/-- Intraproductions are periodic. -/
theorem intraprod_periodic : IsPeriodic γ.intraprod := by
  refine ⟨⟨0, ?_, ?_⟩, ?_⟩
  · rw [zero_smul]
  · rw [zero_smul]
  · rintro h ⟨n, a, b⟩ h' ⟨n', a', b'⟩
    refine ⟨n + n', ?_, ?_⟩
    · rw [add_smul]; exact reach_add a a'
    · rw [add_smul]; exact reach_add b b'

/-- **Lemma 5.5**: `Q_γ + H_γ ⊆ Q_γ`. -/
theorem Q_add_intraprod {q h : VASConfig ι} (hq : q ∈ γ.Q) (hh : h ∈ γ.intraprod) :
    q + h ∈ γ.Q := by
  obtain ⟨n, u, v⟩ := (mem_Q_iff γ).1 hq
  obtain ⟨n', u', v'⟩ := hh
  refine (mem_Q_iff γ).2 ⟨n + n', ?_, ?_⟩
  · have h1 : V.Reach (γ.c + (n + n') • γ.x) (h + (γ.c + n • γ.x)) :=
      reach_cast (Reach.add_left u' (n • γ.x)) (by rw [add_smul]; abel) (by abel)
    exact h1.trans (reach_cast (Reach.add_left u h) rfl (add_comm _ _))
  · have h1 : V.Reach (q + h) (n • γ.y + (γ.c + h)) :=
      reach_cast (Reach.add_left v h) (add_comm _ _) (by abel)
    exact h1.trans (reach_cast (Reach.add_left v' (n • γ.y)) rfl (by rw [add_smul]; abel))

/-- **Lemma 5.6**: for `q ≤ q'` in `Q_γ` there is `h ∈ H_γ` with `q' ≤ q + h`. -/
theorem exists_intraprod_ge {q q' : VASConfig ι} (hq : q ∈ γ.Q) (hq' : q' ∈ γ.Q) (hle : q ≤ q') :
    ∃ h ∈ γ.intraprod, q' ≤ q + h := by
  obtain ⟨m, u, v⟩ := (mem_Q_iff γ).1 hq
  obtain ⟨m', u', v'⟩ := (mem_Q_iff γ).1 hq'
  have hd : q + (q' - q) = q' := by
    funext i
    simp only [Pi.add_apply, Pi.sub_apply]
    exact Nat.add_sub_cancel' (hle i)
  set d := q' - q with hd_def
  refine ⟨d + m • γ.x + m • γ.y, ⟨m + m', ?_, ?_⟩, ?_⟩
  · have h1 : V.Reach (γ.c + (m + m') • γ.x) (m • γ.x + q') :=
      reach_cast (Reach.add_left u' (m • γ.x)) (by rw [add_smul]; abel) rfl
    refine h1.trans (reach_cast (Reach.add_left v (d + m • γ.x)) ?_ ?_)
    · rw [← hd]; abel
    · abel
  · have h1 : V.Reach (γ.c + (d + m • γ.x + m • γ.y)) (d + m • γ.y + q) :=
      reach_cast (Reach.add_left u (d + m • γ.y)) (by abel) rfl
    refine h1.trans (reach_cast (Reach.add_left v' (m • γ.y)) ?_ ?_)
    · rw [← hd]; abel
    · rw [add_smul]; abel
  · calc q' = q + d := hd.symm
      _ ≤ q + d + (m • γ.x + m • γ.y) := fun i => Nat.le_add_right _ _
      _ = q + (d + m • γ.x + m • γ.y) := by abel

/-- Adding multiples of an intraproduction to the capacity stays in `Q_γ`. -/
theorem c_add_nsmul_mem_Q {h : VASConfig ι} (hh : h ∈ γ.intraprod) (k : ℕ) :
    γ.c + k • h ∈ γ.Q := by
  induction k with
  | zero => rw [zero_smul, add_zero]; exact c_mem_Q γ
  | succ k ih => rw [succ_nsmul, ← add_assoc]; exact Q_add_intraprod γ ih hh

/-- Intraproductions vanish on the bounded components. -/
theorem intraprod_apply_eq_zero {h : VASConfig ι} (hh : h ∈ γ.intraprod) {i : ι}
    (hi : i ∈ γ.bounded) : h i = 0 := by
  by_contra hne
  have hpos : 0 < h i := Nat.pos_of_ne_zero hne
  refine (Set.infinite_of_injective_forall_mem (f := fun k : ℕ => γ.c i + k * h i)
    (s := (fun q : VASConfig ι => q i) '' γ.Q) (fun k k' hk => ?_) (fun k => ?_)) hi
  · exact Nat.eq_of_mul_eq_mul_right hpos (Nat.add_left_cancel hk)
  · exact ⟨γ.c + k • h, c_add_nsmul_mem_Q γ hh k, by
      simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]⟩

/-- Every unbounded component is positive for some intraproduction. -/
theorem exists_intraprod_pos [Finite ι] {i : ι} (hi : i ∉ γ.bounded) :
    ∃ h ∈ γ.intraprod, 0 < h i := by
  have hS : ((fun q : VASConfig ι => q i) '' γ.Q).Infinite := hi
  have hex : ∀ k, ∃ q ∈ γ.Q,
      q i = Nat.nth (fun n => n ∈ (fun q : VASConfig ι => q i) '' γ.Q) k :=
    fun k => Nat.nth_mem_of_infinite (p := fun n => n ∈ (fun q : VASConfig ι => q i) '' γ.Q) hS k
  choose q hqQ hqi using hex
  obtain ⟨m, n, hmn, hle⟩ := wellQuasiOrdered_le q
  have hlt : q m i < q n i := by
    rw [hqi, hqi]
    exact Nat.nth_strictMono (p := fun n => n ∈ (fun q : VASConfig ι => q i) '' γ.Q) hS hmn
  obtain ⟨h, hh, hge⟩ := exists_intraprod_ge γ (hqQ m) (hqQ n) hle
  have : q n i ≤ q m i + h i := hge i
  exact ⟨h, hh, by omega⟩

/-- **Lemma 5.7**: there is an intraproduction positive exactly on the unbounded components. -/
theorem exists_intraprod_support [Finite ι] :
    ∃ h ∈ γ.intraprod, γ.bounded = {i | h i = 0} := by
  classical
  have := Fintype.ofFinite ι
  choose! hf hmem hpos using fun i (hi : i ∉ γ.bounded) => exists_intraprod_pos γ hi
  have hsum : ∑ i ∈ Finset.univ.filter (· ∉ γ.bounded), hf i ∈ γ.intraprod :=
    Finset.sum_induction hf (· ∈ γ.intraprod)
      (fun a b ha hb => (intraprod_periodic γ).2 a ha b hb) (intraprod_periodic γ).1
      (fun i hi => hmem i (Finset.mem_filter.1 hi).2)
  refine ⟨_, hsum, Set.ext fun i => ⟨intraprod_apply_eq_zero γ hsum, fun hi => ?_⟩⟩
  by_contra hb
  have h1 : hf i i ≤ (∑ j ∈ Finset.univ.filter (· ∉ γ.bounded), hf j) i := by
    rw [Finset.sum_apply]
    exact Finset.single_le_sum (f := fun j => hf j i) (fun _ _ => Nat.zero_le _)
      (Finset.mem_filter.2 ⟨Finset.mem_univ i, hb⟩)
  have := hpos i hb
  have h3 : (∑ j ∈ Finset.univ.filter (· ∉ γ.bounded), hf j) i = 0 := hi
  omega

end Triple

end VAS

end Cslib
