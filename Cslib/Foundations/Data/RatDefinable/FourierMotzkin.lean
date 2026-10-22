/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Foundations.Data.RatDefinable.Basic
public import Mathlib.Algebra.Order.Field.Basic
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Positivity
public import Mathlib.Data.Fintype.Sum

/-!
# Fourier–Motzkin elimination

We prove that `RatDefinable` sets are closed under projection (`RatDefinable.proj`), i.e. that the
first-order theory of `(ℚ; +, ≤, 0)` admits quantifier elimination in the form of the
Fourier–Motzkin method.

The one-variable step is the explicit algorithm `elimSystem`, acting on a system (list) of
constraints on `κ → ℚ` and eliminating the coordinate `a : κ`: constraints with zero coefficient
for `a` are kept, and every constraint with positive coefficient (a lower bound) is combined with
every constraint with negative coefficient (an upper bound) by cross multiplication. The
correctness theorem is `exists_holds_iff_elimSystem`. The general projection follows by induction
on the (finite) set of eliminated coordinates.

## Main results

* `elimSystem`, `exists_holds_iff_elimSystem`: one step of Fourier–Motzkin elimination.
* `RatDefinable.proj_one`: projection of one coordinate.
* `RatDefinable.proj_finset`: projection of a finite set of coordinates.
* `RatDefinable.proj`: projection along a `Sum` decomposition of the coordinates.

## References

* <https://en.wikipedia.org/wiki/Fourier%E2%80%93Motzkin_elimination>
-/

@[expose] public section

namespace Cslib

/-! ### Witnesses for a system of one-variable constraints -/

/-- Monotone constraints that are individually satisfiable together with `Y` are jointly
satisfiable together with `Y`: take the largest witness. -/
private theorem exists_forall_of_monotone {α β : Type*} [LinearOrder α] {Y : α → Prop}
    (hY : ∃ y, Y y) (l : List β) (p : β → α → Prop) (hp : ∀ b ∈ l, ∀ x y, x ≤ y → p b x → p b y)
    (h : ∀ b ∈ l, ∃ y, Y y ∧ p b y) : ∃ y, Y y ∧ ∀ b ∈ l, p b y := by
  induction l with
  | nil => simpa using hY
  | cons b l ih =>
    obtain ⟨y₁, hy₁, h₁⟩ := ih (fun c hc => hp c (by simp [hc])) (fun c hc => h c (by simp [hc]))
    obtain ⟨y₂, hy₂, h₂⟩ := h b (by simp)
    rcases le_total y₁ y₂ with hle | hle
    · refine ⟨y₂, hy₂, List.forall_mem_cons.2 ⟨h₂, fun c hc => ?_⟩⟩
      exact hp c (by simp [hc]) _ _ hle (h₁ c hc)
    · exact ⟨y₁, hy₁, List.forall_mem_cons.2 ⟨hp b (by simp) _ _ hle h₂, h₁⟩⟩

/-- One-dimensional Helly property: if every lower bound `p ∈ P` (a monotone predicate) and every
upper bound `n ∈ N` (an antitone predicate) are satisfiable, and each pair is satisfiable together,
then all of them are satisfiable together. -/
private theorem exists_forall_of_pairs {β : Type*} (P N : List β) (q : β → ℚ → Prop)
    (hP : ∀ p ∈ P, Monotone (q p)) (hN : ∀ n ∈ N, Antitone (q n))
    (h₀ : ∀ b ∈ P ++ N, ∃ y, q b y) (h : ∀ p ∈ P, ∀ n ∈ N, ∃ y, q p y ∧ q n y) :
    ∃ y, ∀ b ∈ P ++ N, q b y := by
  -- `exists_forall_of_monotone` over `ℚᵒᵈ` takes the smallest witness
  have hN' : ∀ n ∈ N, ∀ x y : ℚᵒᵈ, x ≤ y → q n x → q n y := fun n hn x y hxy hx => hN n hn hxy hx
  have hlow : ∀ p ∈ P, ∃ y, (∀ n ∈ N, q n y) ∧ q p y := fun p hp => by
    obtain ⟨y, hy, hyn⟩ := exists_forall_of_monotone (α := ℚᵒᵈ) (Y := q p) (h₀ p (by simp [hp]))
      N q hN' fun n hn => h p hp n hn
    exact ⟨y, hyn, hy⟩
  obtain ⟨y₀, -, hy₀⟩ := exists_forall_of_monotone (α := ℚᵒᵈ) (Y := fun _ => True) ⟨0, trivial⟩
    N q hN' fun n hn => (h₀ n (by simp [hn])).imp fun _ => (⟨trivial, ·⟩)
  obtain ⟨y, hyN, hyP⟩ := exists_forall_of_monotone (Y := fun y => ∀ n ∈ N, q n y) ⟨y₀, hy₀⟩ P q
    (fun p hp _ _ hxy hx => hP p hp hxy hx) hlow
  exact ⟨y, fun b hb => (List.mem_append.1 hb).elim (hyP b) (hyN b)⟩

/-- The density argument over `ℚ`: a lower bound `cp * y + Lp` and an upper bound `cn * y + Ln`
(with `0 < cp` and `cn < 0`) whose cross-multiplied combination holds admit a common witness
(the midpoint of the two roots). -/
private theorem exists_between {σ τ : Bool} {cp cn Lp Ln : ℚ} (hp : 0 < cp) (hn : cn < 0)
    (h : StrictRel (σ || τ) (-cn * Lp + cp * Ln)) :
    ∃ y, StrictRel σ (cp * y + Lp) ∧ StrictRel τ (cn * y + Ln) := by
  have hcn : cn ≠ 0 := hn.ne
  have hcp : cp ≠ 0 := hp.ne'
  have hn' : 0 < -cn := by linarith
  refine ⟨(cn * Lp + cp * Ln) / (-2 * cp * cn), ?_, ?_⟩
  · convert h.left.mul_pos (c := 1 / (2 * -cn)) (by positivity) using 1
    field_simp
    ring
  · convert h.right.mul_pos (c := 1 / (2 * cp)) (by positivity) using 1
    field_simp
    ring

/-! ### One step of elimination -/

section Step

variable {κ : Type*} [Fintype κ]

/-- The combination `(-n_a) • p + p_a • n` of a lower bound `p` and an upper bound `n` on the
coordinate `a`: it has coefficient `0` at `a`. -/
def LinCons.comb (a : κ) (p n : LinCons κ) : LinCons κ :=
  ⟨fun i => -n.coeff a * p.coeff i + p.coeff a * n.coeff i, p.strict || n.strict⟩

/-- **Fourier–Motzkin elimination** of the coordinate `a` from a system of constraints. -/
def elimSystem (a : κ) (s : List (LinCons κ)) : List (LinCons κ) :=
  s.filter (·.coeff a = 0) ++
    (s.filter (0 < ·.coeff a)).flatMap fun p => (s.filter (·.coeff a < 0)).map (p.comb a)

@[simp] theorem LinCons.eval_comb (a : κ) (p n : LinCons κ) (v : κ → ℚ) :
    (p.comb a n).eval v = -n.coeff a * p.eval v + p.coeff a * n.eval v := by
  simp only [eval, comb, Int.cast_add, Int.cast_mul, Int.cast_neg, add_mul, Finset.sum_add_distrib,
    Finset.mul_sum, mul_assoc]

variable [DecidableEq κ]

open Function

/-- Changing the coordinate `a` of `v` to `y` changes a constraint by a linear function of `y`. -/
theorem LinCons.eval_update (a : κ) (g : LinCons κ) (v : κ → ℚ) (y : ℚ) :
    g.eval (update v a y) = g.coeff a * y + (g.eval v - g.coeff a * v a) := by
  have : update v a y = v + Pi.single a (y - v a) := by
    ext i
    by_cases h : i = a <;> simp [h]
  simp [eval, this, mul_add, Finset.sum_add_distrib, Pi.single_apply]
  ring

/-- A constraint at `v` with the coordinate `a` replaced by `y` is a constraint on `y`. -/
theorem LinCons.holds_update (a : κ) (g : LinCons κ) (v : κ → ℚ) (y : ℚ) :
    g.Holds (update v a y) ↔
      StrictRel g.strict (g.coeff a * y + (g.eval v - g.coeff a * v a)) := by
  rw [Holds, eval_update]

variable {a : κ} {g p n : LinCons κ} {v : κ → ℚ}

theorem LinCons.monotone_holds_update (hg : 0 < g.coeff a) :
    Monotone fun y => g.Holds (update v a y) := fun x y hxy hx => by
  have : (0 : ℚ) < g.coeff a := Int.cast_pos.2 hg
  exact (g.holds_update a v y).2 (((g.holds_update a v x).1 hx).mono (by nlinarith))

theorem LinCons.antitone_holds_update (hg : g.coeff a < 0) :
    Antitone fun y => g.Holds (update v a y) := fun x y hxy hx => by
  have : (g.coeff a : ℚ) < 0 := Int.cast_lt_zero.2 hg
  exact (g.holds_update a v x).2 (((g.holds_update a v y).1 hx).mono (by nlinarith))

theorem LinCons.exists_holds_update (hg : g.coeff a ≠ 0) : ∃ y, g.Holds (update v a y) := by
  have : (g.coeff a : ℚ) ≠ 0 := Int.cast_ne_zero.2 hg
  refine ⟨(1 - (g.eval v - g.coeff a * v a)) / g.coeff a, ?_⟩
  rw [LinCons.holds_update]
  refine StrictRel.of_pos ?_
  rw [mul_div_cancel₀ _ this]
  linarith

/-- The combination of a lower and an upper bound holds iff the two bounds have a common
solution. -/
theorem LinCons.holds_comb_iff (hp : 0 < p.coeff a) (hn : n.coeff a < 0) :
    (p.comb a n).Holds v ↔ ∃ y, p.Holds (update v a y) ∧ n.Holds (update v a y) := by
  have hp' : (0 : ℚ) < p.coeff a := Int.cast_pos.2 hp
  have hn' : (n.coeff a : ℚ) < 0 := Int.cast_lt_zero.2 hn
  have e : (p.comb a n).Holds v ↔ StrictRel (p.strict || n.strict)
      (-n.coeff a * (p.eval v - p.coeff a * v a) + p.coeff a * (n.eval v - n.coeff a * v a)) := by
    rw [LinCons.Holds, LinCons.eval_comb]
    exact iff_of_eq (by congr 1; ring)
  simp only [e, LinCons.holds_update]
  refine ⟨exists_between hp' hn', fun ⟨y, hpy, hny⟩ => ?_⟩
  convert (hpy.mul_pos (neg_pos.2 hn')).add (hny.mul_pos hp') using 1
  ring

/-- **Correctness of one Fourier–Motzkin step**: the system `s` has a solution agreeing with `v`
outside the coordinate `a` iff `v` solves the eliminated system. -/
theorem exists_holds_iff_elimSystem (a : κ) (s : List (LinCons κ)) (v : κ → ℚ) :
    (∃ y, ∀ g ∈ s, g.Holds (update v a y)) ↔ ∀ t ∈ elimSystem a s, t.Holds v := by
  simp only [elimSystem, List.forall_mem_append, List.forall_mem_flatMap, List.forall_mem_map,
    List.mem_filter, decide_eq_true_eq, and_imp]
  constructor
  · rintro ⟨y, h⟩
    refine ⟨fun t ht h0 => ?_, fun p hp hpa n hn hna => ?_⟩
    · simpa [LinCons.Holds, h0] using (LinCons.holds_update a t v y).1 (h t ht)
    · exact (LinCons.holds_comb_iff hpa hna).2 ⟨y, h p hp, h n hn⟩
  · rintro ⟨hz, hc⟩
    obtain ⟨y, hy⟩ := exists_forall_of_pairs (s.filter (0 < ·.coeff a)) (s.filter (·.coeff a < 0))
      (fun g y => g.Holds (update v a y))
      (by simp +contextual [LinCons.monotone_holds_update])
      (by simp +contextual [LinCons.antitone_holds_update])
      (by simp only [List.mem_append, List.mem_filter, decide_eq_true_eq]
          rintro g (⟨-, hg⟩ | ⟨-, hg⟩) <;> exact LinCons.exists_holds_update (by omega))
      (by simp only [List.mem_filter, decide_eq_true_eq]
          rintro p ⟨hp, hpa⟩ n ⟨hn, hna⟩
          exact (LinCons.holds_comb_iff hpa hna).1 (hc p hp hpa n hn hna))
    refine ⟨y, fun g hg => ?_⟩
    rcases lt_trichotomy (g.coeff a) 0 with h0 | h0 | h0
    · exact hy g (by simp [List.mem_append, hg, h0])
    · exact (LinCons.holds_update a g v y).2 (by simpa [LinCons.Holds, h0] using hz g hg h0)
    · exact hy g (by simp [List.mem_append, hg, h0])

end Step

/-! ### Projection of definable sets -/

namespace RatDefinable

open Function

variable {κ : Type*} [Fintype κ]

/-- Projection of one coordinate `a`: the set of `v` that can be completed to an element of `C`
by changing only the coordinate `a`. -/
theorem proj_one [DecidableEq κ] (a : κ) {C : Set (κ → ℚ)} (hC : RatDefinable C) :
    RatDefinable {v : κ → ℚ | ∃ y : ℚ, update v a y ∈ C} := by
  obtain ⟨S, rfl⟩ := hC
  refine ⟨S.map (elimSystem a), ?_⟩
  ext v
  simp only [Set.mem_ofPred_eq, List.mem_map]
  constructor
  · rintro ⟨y, s, hs, h⟩
    exact ⟨elimSystem a s, ⟨s, hs, rfl⟩, (exists_holds_iff_elimSystem a s v).1 ⟨y, h⟩⟩
  · rintro ⟨_, ⟨s, hs, rfl⟩, h⟩
    obtain ⟨y, hy⟩ := (exists_holds_iff_elimSystem a s v).2 h
    exact ⟨y, s, hs, hy⟩

/-- Projection of a finite set `s` of coordinates: the set of `v` that agree outside `s` with some
element of `C`. -/
theorem proj_finset (s : Finset κ) {C : Set (κ → ℚ)} (hC : RatDefinable C) :
    RatDefinable {v : κ → ℚ | ∃ w ∈ C, ∀ i ∉ s, w i = v i} := by
  classical
  induction s using Finset.induction_on generalizing C with
  | empty => convert hC using 1; ext; simp [← funext_iff]
  | insert a s ha ih =>
    convert ih (proj_one a hC) using 1
    ext v
    simp only [Set.mem_ofPred_eq, Finset.mem_insert, not_or, and_imp]
    constructor
    · rintro ⟨w, hw, h⟩
      refine ⟨update w a (v a), ⟨w a, by simpa using hw⟩, fun i hi => ?_⟩
      grind [update_apply]
    · rintro ⟨w, ⟨y, hy⟩, h⟩
      exact ⟨update w a y, hy, fun i hi hi' => by grind [update_apply]⟩

/-- **Quantifier elimination for `(ℚ; +, ≤)`** (Fourier–Motzkin): the projection of a definable set
along finitely many coordinates is definable. -/
theorem proj {κ' : Type*} [Fintype κ'] {C : Set (κ ⊕ κ' → ℚ)}
    (hC : RatDefinable C) : RatDefinable {v : κ → ℚ | ∃ w : κ' → ℚ, Sum.elim v w ∈ C} := by
  classical
  -- extend `v` by zero on the eliminated coordinates
  convert (proj_finset (Finset.univ.image Sum.inr) hC).preimage
    (fun j i => if i = Sum.inl j then 1 else 0) using 1
  ext v
  simp only [Set.mem_ofPred_eq]
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨_, hw, fun i hi => by cases i <;> simp_all⟩
  · rintro ⟨w, hw, h⟩
    refine ⟨fun k => w (.inr k), ?_⟩
    convert hw using 1
    ext (i | i)
    · simpa using (h (.inl i) (by simp)).symm
    · rfl

end RatDefinable

end Cslib
