/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Presburger.Semantics
public import Mathlib.Data.Nat.GCD.Basic
public import Mathlib.Algebra.Order.Ring.Int
public import Mathlib.Algebra.GroupWithZero.Basic

/-! # Cooper's elimination of one existential quantifier

Given a quantifier-free formula `φ` over the variables `x₀, x₁, …` we construct a quantifier-free
formula `QF.elim φ` over the variables `x₁, x₂, …` (renumbered to `x₀, x₁, …`) such that
`QF.elim φ` holds iff `∃ x₀, φ` holds. The method is Cooper's:

1. *Negations are pushed to the atoms* by `QF.neg` (`¬ t ≤ 0` is `1 - t ≤ 0` over `ℤ`, and
   `¬ (m + 1) ∣ t` is a disjunction of `(m + 1) ∣ t - r`, `0 < r ≤ m`). Thus `QF` is positive.
2. *Unit coefficients*: let `L` be the lcm of the absolute values of the coefficients of `x₀`.
   Multiplying every atom by a suitable factor and substituting `y = L * x₀`
   (`QF.norm`) makes all coefficients of `y` lie in `{-1, 0, 1}`, at the price of the extra
   conjunct `L ∣ y`.
3. *Cooper's theorem* (`QF.eval_cooper`): for a positive formula `φ` with unit coefficients and
   `δ` the lcm of its moduli,
   `∃ y, φ(y)` iff `⋁_{j = 1}^{δ} φ_{-∞}(j) ∨ ⋁_{b ∈ B} ⋁_{j = 0}^{δ - 1} φ(b + j)`,
   where `φ_{-∞}` (`QF.minf`) replaces the atoms `y + r ≤ 0` by `true` and `-y + r ≤ 0` by `false`,
   and `B` (`QF.bset`) is the list of the lower bounds `r` of the atoms `-y + r ≤ 0`.

## Complexity

Each elimination multiplies the size of the formula by up to `δ * (|B| + 1)` and the numbers by
the lcm `L`; the worst case of the whole procedure is triply exponential in the formula size. No
optimisation is attempted.

## Main definitions

- `Presburger.QF.neg`: the negation of a formula, again as a positive formula.
- `Presburger.QF.elim`: the quantifier-free equivalent of `∃ x₀, φ`.

## Main statements

- `Presburger.QF.eval_neg`: `QF.neg` is semantic negation.
- `Presburger.QF.eval_norm`: the coefficient normalisation is sound.
- `Presburger.QF.eval_cooper`: Cooper's theorem.
- `Presburger.QF.eval_elim`: `(φ.elim).eval v ↔ ∃ x, φ.eval (cons x v)`.
-/

@[expose] public section

namespace Cslib.Presburger

namespace QF

/-- The false formula. -/
def ff : QF := le (Term.ofInt 1)

/-- The true formula. -/
def tt : QF := le (Term.ofInt 0)

@[simp] theorem eval_ff (v : ℕ → ℤ) : ¬ ff.eval v := by
  simp only [ff, eval, Term.eval_ofInt]; omega

@[simp] theorem eval_tt (v : ℕ → ℤ) : tt.eval v := by
  simp only [tt, eval, Term.eval_ofInt]; omega

/-- The disjunction of a list of formulas. -/
def bigOr (l : List QF) : QF := l.foldr or ff

theorem eval_bigOr (v : ℕ → ℤ) (l : List QF) : (bigOr l).eval v ↔ ∃ φ ∈ l, φ.eval v := by
  induction l with
  | nil => simp only [bigOr, List.foldr_nil, eval_ff, List.not_mem_nil, false_and, exists_false]
  | cons φ l ih => simp only [bigOr, List.foldr_cons, eval, ← ih, List.mem_cons, exists_eq_or_imp]

/-- The negation of `(m + 1) ∣ t`: the residue of `t` modulo `m + 1` is some `r ∈ [1, m]`. -/
def negDvd (m : ℕ) (t : Term) : QF :=
  bigOr ((List.range m).map fun r : ℕ => dvd m (t + Term.ofInt (-((r : ℤ) + 1))))

theorem eval_negDvd (v : ℕ → ℤ) (m : ℕ) (t : Term) :
    (negDvd m t).eval v ↔ ¬ ((m : ℤ) + 1) ∣ t.eval v := by
  simp only [negDvd, eval_bigOr, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨r, hr, rfl⟩, h⟩ hd
    simp only [eval, Term.eval_add, Term.eval_ofInt] at h
    have := Int.le_of_dvd (by omega) (Int.dvd_neg.1 ((Int.dvd_add_right hd).1 h))
    omega
  · intro hd
    have hpos : 0 < (m : ℤ) + 1 := by omega
    have hne : t.eval v % ((m : ℤ) + 1) ≠ 0 := fun h => hd (Int.dvd_of_emod_eq_zero h)
    have h0 := Int.emod_nonneg (t.eval v) hpos.ne'
    have h1 := Int.emod_lt_of_pos (t.eval v) hpos
    refine ⟨_, ⟨(t.eval v % ((m : ℤ) + 1) - 1).toNat, by omega, rfl⟩, ?_⟩
    simp only [eval, Term.eval_add, Term.eval_ofInt]
    rw [Int.toNat_of_nonneg (by omega), show t.eval v + -(t.eval v % ((m : ℤ) + 1) - 1 + 1) =
      t.eval v - t.eval v % ((m : ℤ) + 1) by ring]
    exact Int.dvd_self_sub_emod

/-- The negation of a formula, as a positive formula. -/
def neg : QF → QF
  | le t => le (Term.ofInt 1 - t)
  | dvd m t => negDvd m t
  | and φ ψ => or φ.neg ψ.neg
  | or φ ψ => and φ.neg ψ.neg

theorem eval_neg (v : ℕ → ℤ) (φ : QF) : φ.neg.eval v ↔ ¬ φ.eval v := by
  induction φ with
  | le t => simp only [neg, eval, Term.eval_sub, Term.eval_ofInt]; omega
  | dvd m t => exact eval_negDvd v m t
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => simp only [neg, eval, ihφ, ihψ]; tauto

end QF

namespace Term

/-- Substitute the term `s` for the variable `x₀` in `t`, and renumber the other variables. -/
def subst0 (t s : Term) : Term := t.rest + smul t.coef0 s

theorem eval_subst0 (v : ℕ → ℤ) (t s : Term) :
    (t.subst0 s).eval v = t.eval (cons (s.eval v) v) := by
  rw [eval_cons, subst0, eval_add, eval_smul]; ring

end Term

namespace QF

/-- Substitute the term `s` for the variable `x₀` and renumber the other variables. -/
def subst (s : Term) : QF → QF
  | le t => le (t.subst0 s)
  | dvd m t => dvd m (t.subst0 s)
  | and φ ψ => and (φ.subst s) (ψ.subst s)
  | or φ ψ => or (φ.subst s) (ψ.subst s)

theorem eval_subst (v : ℕ → ℤ) (s : Term) (φ : QF) :
    (φ.subst s).eval v ↔ φ.eval (cons (s.eval v) v) := by
  induction φ with
  | le t => simp only [subst, eval, Term.eval_subst0]
  | dvd m t => simp only [subst, eval, Term.eval_subst0]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => simp only [subst, eval, ihφ, ihψ]

/-! ### Normalisation of the coefficients of `x₀` -/

end QF

namespace Term

/-- The absolute value of the coefficient of `x₀`, with `0` replaced by `1`. -/
def absCoef (t : Term) : ℕ := max 1 t.coef0.natAbs

theorem absCoef_pos (t : Term) : 0 < t.absCoef := lt_of_lt_of_le Nat.one_pos (le_max_left _ _)

/-- The factor by which `t` has to be multiplied to get a coefficient `± L` of `x₀`. -/
def mult (L : ℕ) (t : Term) : ℕ := L / t.absCoef

/-- Multiply `t` by `mult L t` and replace `L * x₀` by a new variable `y = x₀`, so that the
coefficient of `y` is `±1` or `0`. -/
def scale (L : ℕ) (t : Term) : Term :=
  ⟨(t.mult L : ℤ) * t.const, t.coef0.sign :: t.rest.coeffs.map ((t.mult L : ℤ) * ·)⟩

theorem mult_pos {L : ℕ} (t : Term) (hL : 0 < L) (h : t.absCoef ∣ L) : 0 < t.mult L :=
  Nat.div_pos (Nat.le_of_dvd hL h) t.absCoef_pos

theorem sign_mul_eq {L : ℕ} (t : Term) (h : t.absCoef ∣ L) :
    t.coef0.sign * (L : ℤ) = (t.mult L : ℤ) * t.coef0 := by
  by_cases ha : t.coef0 = 0
  · simp only [ha, Int.sign_zero, zero_mul, mul_zero]
  · have habs : t.absCoef = t.coef0.natAbs := by
      simp only [absCoef]; exact max_eq_right (Int.natAbs_pos.2 ha)
    rw [habs] at h
    obtain ⟨q, hq⟩ := h
    have hm : t.mult L = q := by
      simp only [mult, habs, hq]
      exact Nat.mul_div_cancel_left _ (Int.natAbs_pos.2 ha)
    have hq' : (L : ℤ) = (t.coef0.natAbs : ℤ) * q := by exact_mod_cast hq
    rw [hm, hq']
    have := Int.sign_mul_natAbs t.coef0
    calc t.coef0.sign * ((t.coef0.natAbs : ℤ) * q)
        = (t.coef0.sign * t.coef0.natAbs) * q := by ring
      _ = q * t.coef0 := by rw [this]; ring

theorem eval_scale {L : ℕ} (t : Term) (h : t.absCoef ∣ L) (x : ℤ) (v : ℕ → ℤ) :
    (t.scale L).eval (cons ((L : ℤ) * x) v) = (t.mult L : ℤ) * t.eval (cons x v) := by
  have h1 : (t.scale L).coef0 = t.coef0.sign := rfl
  have h2 : (t.scale L).rest.eval v = (t.mult L : ℤ) * t.rest.eval v := by
    simp only [eval, scale, rest, List.tail_cons, evalCoeffs_map_mul]
    ring
  rw [eval_cons, h1, h2, eval_cons]
  have := t.sign_mul_eq h
  calc t.coef0.sign * ((L : ℤ) * x) + (t.mult L : ℤ) * t.rest.eval v
      = (t.coef0.sign * (L : ℤ)) * x + (t.mult L : ℤ) * t.rest.eval v := by ring
    _ = _ := by rw [this]; ring

end Term

namespace QF

/-- The least common multiple of the absolute values of the coefficients of `x₀`. -/
def lcmCoef : QF → ℕ
  | le t => t.absCoef
  | dvd _ t => t.absCoef
  | and φ ψ => Nat.lcm φ.lcmCoef ψ.lcmCoef
  | or φ ψ => Nat.lcm φ.lcmCoef ψ.lcmCoef

theorem lcmCoef_pos (φ : QF) : 0 < φ.lcmCoef := by
  induction φ with
  | le t => exact t.absCoef_pos
  | dvd m t => exact t.absCoef_pos
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => exact Nat.lcm_pos ihφ ihψ

/-- Multiply every atom by the factor that turns the coefficient of `x₀` into `± L`, and read
`L * x₀` as a new variable `y`. -/
def norm (L : ℕ) : QF → QF
  | le t => le (t.scale L)
  | dvd m t => dvd (t.mult L * (m + 1) - 1) (t.scale L)
  | and φ ψ => and (φ.norm L) (ψ.norm L)
  | or φ ψ => or (φ.norm L) (ψ.norm L)

theorem eval_norm {L : ℕ} (hL : 0 < L) (x : ℤ) (v : ℕ → ℤ) (φ : QF) (h : φ.lcmCoef ∣ L) :
    (φ.norm L).eval (cons ((L : ℤ) * x) v) ↔ φ.eval (cons x v) := by
  induction φ with
  | le t =>
    have hm : (0 : ℤ) < t.mult L := by exact_mod_cast t.mult_pos hL h
    simp only [norm, eval, t.eval_scale h]
    constructor
    · intro h1; by_contra h2; have h2 := not_le.1 h2; nlinarith
    · intro h1; nlinarith
  | dvd m t =>
    have hm : 0 < t.mult L := t.mult_pos hL h
    have hm' : (t.mult L : ℤ) ≠ 0 := by exact_mod_cast hm.ne'
    simp only [norm, eval, t.eval_scale h]
    have : ((t.mult L * (m + 1) - 1 : ℕ) : ℤ) + 1 = (t.mult L : ℤ) * ((m : ℤ) + 1) := by
      have : 1 ≤ t.mult L * (m + 1) := Nat.mul_pos hm (Nat.succ_pos m)
      push_cast [Nat.cast_sub this]
      ring
    rw [this, mul_dvd_mul_iff_left hm']
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [norm, eval]
    rw [ihφ (Nat.dvd_trans (Nat.dvd_lcm_left _ _) h), ihψ (Nat.dvd_trans (Nat.dvd_lcm_right _ _) h)]

/-- All coefficients of `x₀` are `-1`, `0` or `1`. -/
def UnitCoef : QF → Prop
  | le t => t.coef0.natAbs ≤ 1
  | dvd _ t => t.coef0.natAbs ≤ 1
  | and φ ψ => UnitCoef φ ∧ UnitCoef ψ
  | or φ ψ => UnitCoef φ ∧ UnitCoef ψ

theorem unitCoef_scale (L : ℕ) (t : Term) : (t.scale L).coef0.natAbs ≤ 1 := by
  change t.coef0.sign.natAbs ≤ 1
  rcases lt_trichotomy t.coef0 0 with h | h | h
  · simp only [Int.sign_eq_neg_one_of_neg h]; decide
  · simp only [h, Int.sign_zero]; decide
  · simp only [Int.sign_eq_one_of_pos h]; decide

theorem unitCoef_norm (L : ℕ) (φ : QF) : UnitCoef (φ.norm L) := by
  induction φ with
  | le t => exact unitCoef_scale L t
  | dvd m t => exact unitCoef_scale L t
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => exact ⟨ihφ, ihψ⟩

end QF

/-! ### Cooper's theorem -/

namespace QF

/-- The least common multiple of the moduli of the divisibility atoms. -/
def lcmMod : QF → ℕ
  | le _ => 1
  | dvd m _ => m + 1
  | and φ ψ => Nat.lcm φ.lcmMod ψ.lcmMod
  | or φ ψ => Nat.lcm φ.lcmMod ψ.lcmMod

theorem lcmMod_pos (φ : QF) : 0 < φ.lcmMod := by
  induction φ with
  | le t => exact Nat.one_pos
  | dvd m t => exact Nat.succ_pos m
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => exact Nat.lcm_pos ihφ ihψ

/-- The projection at `-∞`: for `x₀` very negative, the atoms `a * x₀ + r ≤ 0` with `a > 0` hold
and those with `a < 0` fail. -/
def minf : QF → QF
  | le t => if 0 < t.coef0 then tt else if t.coef0 < 0 then ff else le t
  | dvd m t => dvd m t
  | and φ ψ => and φ.minf ψ.minf
  | or φ ψ => or φ.minf ψ.minf

/-- The lower bounds `r` of the atoms `-x₀ + r ≤ 0`. -/
def bset : QF → List Term
  | le t => if t.coef0 = -1 then [t.rest] else []
  | dvd _ _ => []
  | and φ ψ => φ.bset ++ ψ.bset
  | or φ ψ => φ.bset ++ ψ.bset

/-- Far enough to the left, `φ` agrees with its projection `minf φ` at `-∞`. -/
theorem exists_minf (v : ℕ → ℤ) (φ : QF) :
    ∃ N : ℤ, ∀ y ≤ N, (φ.minf.eval (cons y v) ↔ φ.eval (cons y v)) := by
  induction φ with
  | le t =>
    refine ⟨-|t.rest.eval v| - 1, fun y hy => ?_⟩
    have hr := neg_abs_le (t.rest.eval v)
    have hr' := le_abs_self (t.rest.eval v)
    by_cases h1 : 0 < t.coef0
    · simp only [minf, h1, ↓reduceIte, eval_tt, true_iff, eval, Term.eval_cons]
      nlinarith
    · by_cases h2 : t.coef0 < 0
      · simp only [minf, h1, ↓reduceIte, h2, eval_ff, false_iff, eval, Term.eval_cons,
          not_le]
        nlinarith
      · simp only [minf, h1, h2, ↓reduceIte]
  | dvd m t => exact ⟨0, fun y _ => Iff.rfl⟩
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    obtain ⟨N₁, h₁⟩ := ihφ
    obtain ⟨N₂, h₂⟩ := ihψ
    exact ⟨min N₁ N₂, fun y hy => by
      simp only [minf, eval]
      rw [h₁ y (le_trans hy (min_le_left _ _)), h₂ y (le_trans hy (min_le_right _ _))]⟩

/-- The projection at `-∞` is periodic with every period divisible by all moduli. -/
theorem eval_minf_add_mul (v : ℕ → ℤ) (φ : QF) {δ : ℕ} (hδ : φ.lcmMod ∣ δ) (y q : ℤ) :
    φ.minf.eval (cons (y + δ * q) v) ↔ φ.minf.eval (cons y v) := by
  induction φ with
  | le t =>
    by_cases h1 : 0 < t.coef0
    · simp only [minf, h1, ↓reduceIte, eval_tt]
    · by_cases h2 : t.coef0 < 0
      · simp only [minf, h1, ↓reduceIte, h2, ↓reduceIte, eval_ff]
      · have h3 : t.coef0 = 0 := by omega
        have e : minf (le t) = le t := by simp only [minf, h1, h2, ↓reduceIte]
        simp only [e, eval, Term.eval_cons, h3]
        omega
  | dvd m t =>
    simp only [minf, eval, Term.eval_cons]
    have h : ((m : ℤ) + 1) ∣ t.coef0 * (δ * q) :=
      Dvd.dvd.mul_left (Dvd.dvd.mul_right (by exact_mod_cast hδ) q) _
    rw [show t.coef0 * (y + δ * q) + t.rest.eval v = (t.coef0 * y + t.rest.eval v) +
      t.coef0 * (δ * q) by ring]
    exact Int.dvd_add_left h
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    simp only [minf, eval]
    rw [ihφ (Nat.dvd_trans (Nat.dvd_lcm_left _ _) hδ),
      ihψ (Nat.dvd_trans (Nat.dvd_lcm_right _ _) hδ)]

/-- If no lower bound lies in `(y - δ, y]`, then a positive formula with unit coefficients that
holds at `y` also holds at `y - δ`. -/
theorem eval_step_down (v : ℕ → ℤ) (φ : QF) (hu : UnitCoef φ) {δ : ℕ} (hδ : φ.lcmMod ∣ δ)
    (y : ℤ) (hB : ∀ b ∈ φ.bset, ¬ (y - δ < b.eval v ∧ b.eval v ≤ y)) :
    φ.eval (cons y v) → φ.eval (cons (y - δ) v) := by
  induction φ with
  | le t =>
    have hc : t.coef0 = -1 ∨ t.coef0 = 0 ∨ t.coef0 = 1 := by
      simp only [UnitCoef] at hu; omega
    have hδ0 : (0 : ℤ) ≤ δ := Int.natCast_nonneg δ
    simp only [eval, Term.eval_cons]
    rcases hc with h | h | h
    · have hb := hB t.rest (by simp only [bset, h, ↓reduceIte, List.mem_singleton])
      intro hh
      simp only [h] at hh ⊢
      by_contra hcon
      exact hb ⟨by linarith, by linarith⟩
    · simp only [h]; intro hh; linarith
    · simp only [h]; intro hh; linarith
  | dvd m t =>
    simp only [eval, Term.eval_cons]
    have h : ((m : ℤ) + 1) ∣ t.coef0 * δ := Dvd.dvd.mul_left (by exact_mod_cast hδ) _
    intro hh
    rw [show t.coef0 * (y - δ) + t.rest.eval v = (t.coef0 * y + t.rest.eval v) - t.coef0 * δ by
      ring]
    exact Int.dvd_sub hh h
  | and φ ψ ihφ ihψ =>
    simp only [eval]
    exact fun ⟨h1, h2⟩ =>
      ⟨ihφ hu.1 (Nat.dvd_trans (Nat.dvd_lcm_left _ _) hδ)
          (fun b hb => hB b (List.mem_append_left _ hb)) h1,
        ihψ hu.2 (Nat.dvd_trans (Nat.dvd_lcm_right _ _) hδ)
          (fun b hb => hB b (List.mem_append_right _ hb)) h2⟩
  | or φ ψ ihφ ihψ =>
    simp only [eval]
    exact fun h => h.imp
      (ihφ hu.1 (Nat.dvd_trans (Nat.dvd_lcm_left _ _) hδ)
        (fun b hb => hB b (List.mem_append_left _ hb)))
      (ihψ hu.2 (Nat.dvd_trans (Nat.dvd_lcm_right _ _) hδ)
        (fun b hb => hB b (List.mem_append_right _ hb)))

/-- Cooper's elimination of `∃ x₀` for a positive formula with unit coefficients of `x₀`. -/
def cooper (φ : QF) : QF :=
  or (bigOr ((List.range φ.lcmMod).map fun j : ℕ => φ.minf.subst (Term.ofInt ((j : ℤ) + 1))))
    (bigOr (φ.bset.flatMap fun b =>
      (List.range φ.lcmMod).map fun j : ℕ => φ.subst (b + Term.ofInt (j : ℤ))))

theorem eval_cooper_left (v : ℕ → ℤ) (φ : QF) (δ : ℕ) :
    (bigOr ((List.range δ).map fun j : ℕ => φ.minf.subst (Term.ofInt ((j : ℤ) + 1)))).eval v ↔
      ∃ j < δ, φ.minf.eval (cons ((j : ℤ) + 1) v) := by
  simp only [eval_bigOr, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, h⟩
    rw [eval_subst, Term.eval_ofInt] at h
    exact ⟨j, hj, h⟩
  · rintro ⟨j, hj, h⟩
    exact ⟨_, ⟨j, hj, rfl⟩, by rw [eval_subst, Term.eval_ofInt]; exact h⟩

theorem eval_cooper_right (v : ℕ → ℤ) (φ : QF) (δ : ℕ) :
    (bigOr (φ.bset.flatMap fun b =>
      (List.range δ).map fun j : ℕ => φ.subst (b + Term.ofInt (j : ℤ)))).eval v ↔
      ∃ b ∈ φ.bset, ∃ j < δ, φ.eval (cons (b.eval v + j) v) := by
  simp only [eval_bigOr, List.mem_flatMap, List.mem_map, List.mem_range]
  constructor
  · rintro ⟨_, ⟨b, hb, j, hj, rfl⟩, h⟩
    rw [eval_subst, Term.eval_add, Term.eval_ofInt] at h
    exact ⟨b, hb, j, hj, h⟩
  · rintro ⟨b, hb, j, hj, h⟩
    exact ⟨_, ⟨b, hb, j, hj, rfl⟩, by rw [eval_subst, Term.eval_add, Term.eval_ofInt]; exact h⟩

/-- **Cooper's theorem.** -/
theorem eval_cooper (v : ℕ → ℤ) (φ : QF) (hu : UnitCoef φ) :
    (cooper φ).eval v ↔ ∃ y, φ.eval (cons y v) := by
  have hδpos := φ.lcmMod_pos
  simp only [cooper, eval, eval_cooper_left, eval_cooper_right]
  generalize hg : φ.lcmMod = δ at hδpos ⊢
  have hδ : φ.lcmMod ∣ δ := hg ▸ dvd_rfl
  obtain ⟨N, hN⟩ := exists_minf v φ
  have hδ1 : (1 : ℤ) ≤ δ := by exact_mod_cast hδpos
  constructor
  · rintro (⟨j, hj, hM⟩ | ⟨b, hb, j, hj, hP⟩)
    · set n : ℕ := ((j : ℤ) + 1 - N).toNat with hn
      have hn1 : (j : ℤ) + 1 - N ≤ n := Int.self_le_toNat _
      have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
      have hy : (j : ℤ) + 1 + δ * (-(n : ℤ)) ≤ N := by nlinarith
      refine ⟨_, (hN _ hy).1 ?_⟩
      exact (eval_minf_add_mul v φ hδ ((j : ℤ) + 1) (-(n : ℤ))).2 hM
    · exact ⟨_, hP⟩
  · rintro ⟨y0, hy0⟩
    by_contra hno
    rw [not_or] at hno
    obtain ⟨hno1, hno2⟩ := hno
    have hall : ∀ n : ℕ, φ.eval (cons (y0 - δ * n) v) := by
      intro n
      induction n with
      | zero => simpa only [Nat.cast_zero, mul_zero, sub_zero] using hy0
      | succ n ih =>
        have hB : ∀ b ∈ φ.bset, ¬ (y0 - δ * n - δ < b.eval v ∧ b.eval v ≤ y0 - δ * n) := by
          rintro b hb ⟨h1, h2⟩
          refine hno2 ⟨b, hb, (y0 - δ * n - b.eval v).toNat, by omega, ?_⟩
          rwa [show b.eval v + ((y0 - δ * n - b.eval v).toNat : ℤ) = y0 - δ * n by omega]
        have := eval_step_down v φ hu hδ _ hB ih
        rwa [show y0 - δ * n - δ = y0 - δ * ((n + 1 : ℕ) : ℤ) by push_cast; ring] at this
    set n : ℕ := (y0 - N).toNat with hn
    have hn1 : y0 - N ≤ n := Int.self_le_toNat _
    have hn0 : (0 : ℤ) ≤ n := Int.natCast_nonneg n
    have hy : y0 - δ * n ≤ N := by nlinarith
    have hM := (hN _ hy).2 (hall n)
    set y := y0 - δ * n with hydef
    have hδ0 : (δ : ℤ) ≠ 0 := by omega
    have h1 := Int.emod_add_mul_ediv (y - 1) δ
    have h2 := Int.emod_nonneg (y - 1) hδ0
    have h3 := Int.emod_lt_of_pos (y - 1) (by omega : (0 : ℤ) < δ)
    refine hno1 ⟨((y - 1) % δ).toNat, by omega, ?_⟩
    have := (eval_minf_add_mul v φ hδ (((y - 1) % δ).toNat + 1) ((y - 1) / δ)).1
    rw [show (((y - 1) % δ).toNat : ℤ) + 1 + δ * ((y - 1) / δ) = y by omega] at this
    exact this hM

/-- Eliminate the variable `x₀`: a quantifier-free formula over the remaining variables, which
(after renumbering them) is equivalent to `∃ x₀, φ`. -/
def elim (φ : QF) : QF :=
  cooper (and (φ.norm φ.lcmCoef) (dvd (φ.lcmCoef - 1) (Term.var 0)))

/-- **Correctness of the elimination of one existential quantifier.** -/
theorem eval_elim (v : ℕ → ℤ) (φ : QF) : φ.elim.eval v ↔ ∃ x : ℤ, φ.eval (cons x v) := by
  have hL := φ.lcmCoef_pos
  have hu : UnitCoef (and (φ.norm φ.lcmCoef) (dvd (φ.lcmCoef - 1) (Term.var 0))) :=
    ⟨unitCoef_norm _ _, show (Term.var 0).coef0.natAbs ≤ 1 by decide⟩
  have hcast : (((φ.lcmCoef - 1 : ℕ) : ℤ) + 1) = φ.lcmCoef := by omega
  rw [elim, eval_cooper v _ hu]
  simp only [eval, Term.eval_var, cons_zero, hcast]
  constructor
  · rintro ⟨y, h1, x, rfl⟩
    exact ⟨x, (eval_norm hL x v φ dvd_rfl).1 h1⟩
  · rintro ⟨x, hx⟩
    exact ⟨_, (eval_norm hL x v φ dvd_rfl).2 hx, x, rfl⟩

end QF

end Cslib.Presburger
