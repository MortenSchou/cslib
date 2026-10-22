/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Presburger.Syntax
public import Mathlib.Algebra.Order.Group.Int
public import Mathlib.Algebra.Ring.Int.Defs
public import Mathlib.Tactic.Ring
public import Mathlib.Tactic.Linarith

/-! # Semantics of Presburger arithmetic

An assignment is a function `ℕ → ℤ`. A quantifier `∃ φ` extends the assignment with a new variable
`0` by `cons`, shifting the old variables up by one.

## Main definitions

- `Presburger.cons`: extend an assignment by a new variable `0`.
- `Presburger.Term.eval`, `Presburger.QF.eval`, `Presburger.PForm.eval`: the semantics.
- `Presburger.QF.holds0`: a Boolean evaluator of quantifier-free formulas at the zero assignment.
- `Presburger.PForm.evalNat`, `Presburger.PForm.natRel`: the natural-number reading of a formula
  and its relativisation to `ℤ`.

## Main statements

- `Presburger.Term.eval_cons`: the effect of the variable `0` on a term.
- `Presburger.PForm.eval_congr`: a formula only depends on the variables below its `bound`.
- `Presburger.PForm.eval_allN`: semantics of the universal closure.
- `Presburger.QF.holds0_iff`: `holds0` evaluates `QF.eval` at the zero assignment.
- `Presburger.PForm.eval_natRel`: natural-number semantics via relativisation.
-/

@[expose] public section

namespace Cslib.Presburger

/-- Extend an assignment with a new variable `0`, shifting the others up by one. -/
def cons (x : ℤ) (v : ℕ → ℤ) : ℕ → ℤ
  | 0 => x
  | n + 1 => v n

@[simp] theorem cons_zero (x : ℤ) (v : ℕ → ℤ) : cons x v 0 = x := rfl

@[simp] theorem cons_succ (x : ℤ) (v : ℕ → ℤ) (n : ℕ) : cons x v (n + 1) = v n := rfl

/-- The value of the linear combination of the variables with the given coefficients. -/
def evalCoeffs : List ℤ → (ℕ → ℤ) → ℤ
  | [], _ => 0
  | a :: as, v => a * v 0 + evalCoeffs as (fun n => v (n + 1))

namespace Term

/-- The value of a term under an assignment. -/
def eval (v : ℕ → ℤ) (t : Term) : ℤ := t.const + evalCoeffs t.coeffs v

theorem eval_cons (x : ℤ) (v : ℕ → ℤ) (t : Term) :
    t.eval (cons x v) = t.coef0 * x + t.rest.eval v := by
  obtain ⟨c, _ | ⟨a, as⟩⟩ := t <;>
    simp only [eval, coef0, rest, evalCoeffs, List.headD_nil, List.tail_nil, List.headD_cons,
      List.tail_cons, cons_zero, cons_succ] <;> ring

theorem evalCoeffs_addCoeffs (as bs : List ℤ) (v : ℕ → ℤ) :
    evalCoeffs (addCoeffs as bs) v = evalCoeffs as v + evalCoeffs bs v := by
  induction as generalizing bs v <;> cases bs <;> grind [addCoeffs, evalCoeffs]

theorem evalCoeffs_map_mul (k : ℤ) (as : List ℤ) (v : ℕ → ℤ) :
    evalCoeffs (as.map (k * ·)) v = k * evalCoeffs as v := by
  induction as generalizing v <;> grind [evalCoeffs]

@[simp] theorem eval_add (v : ℕ → ℤ) (s t : Term) : (s + t).eval v = s.eval v + t.eval v := by
  change s.const + t.const + evalCoeffs (addCoeffs s.coeffs t.coeffs) v = _
  rw [evalCoeffs_addCoeffs]
  simp only [eval]; ring

@[simp] theorem eval_smul (v : ℕ → ℤ) (k : ℤ) (t : Term) :
    (smul k t).eval v = k * t.eval v := by
  change k * t.const + evalCoeffs (t.coeffs.map (k * ·)) v = _
  rw [evalCoeffs_map_mul]
  simp only [eval]; ring

@[simp] theorem eval_neg (v : ℕ → ℤ) (t : Term) : (-t).eval v = -t.eval v := by
  change (smul (-1) t).eval v = _
  rw [eval_smul]; ring

@[simp] theorem eval_sub (v : ℕ → ℤ) (s t : Term) : (s - t).eval v = s.eval v - t.eval v := by
  change (s + -t).eval v = _
  rw [eval_add, eval_neg]; ring

@[simp] theorem eval_ofInt (v : ℕ → ℤ) (c : ℤ) : (ofInt c).eval v = c := by
  simp only [eval, ofInt, evalCoeffs, add_zero]

@[simp] theorem eval_ofNat (v : ℕ → ℤ) (n : ℕ) :
    (OfNat.ofNat n : Term).eval v = n :=
  eval_ofInt v n

@[simp] theorem eval_one (v : ℕ → ℤ) : (1 : Term).eval v = 1 := eval_ofInt v 1

@[simp] theorem eval_zero (v : ℕ → ℤ) : (0 : Term).eval v = 0 := eval_ofInt v 0

theorem evalCoeffs_replicate_zero_append (i : ℕ) (as : List ℤ) (v : ℕ → ℤ) :
    evalCoeffs (List.replicate i 0 ++ as) v = evalCoeffs as (fun n => v (n + i)) := by
  induction i generalizing v with
  | zero => rfl
  | succ i ih =>
    simp only [List.replicate_succ, List.cons_append, evalCoeffs, zero_mul, zero_add, ih]
    rfl

@[simp] theorem eval_var (v : ℕ → ℤ) (i : ℕ) : (var i).eval v = v i := by
  simp only [eval, var, zero_add, evalCoeffs_replicate_zero_append, evalCoeffs, one_mul, add_zero]

theorem evalCoeffs_congr (as : List ℤ) {v w : ℕ → ℤ} (h : ∀ i < as.length, v i = w i) :
    evalCoeffs as v = evalCoeffs as w := by
  induction as generalizing v w with
  | nil => rfl
  | cons a as ih =>
    simp only [evalCoeffs, h 0 (by simp), ih fun i hi => h (i + 1) (by simpa using hi)]

theorem eval_congr (t : Term) {v w : ℕ → ℤ} (h : ∀ i < t.coeffs.length, v i = w i) :
    t.eval v = t.eval w := by
  simp only [eval]; rw [evalCoeffs_congr t.coeffs h]

theorem evalCoeffs_zero (as : List ℤ) : evalCoeffs as (fun _ => 0) = 0 := by
  induction as <;> grind [evalCoeffs]

theorem eval_zeroEnv (t : Term) : t.eval (fun _ => 0) = t.const := by
  simp only [eval, evalCoeffs_zero, add_zero]

end Term

namespace QF

/-- Satisfaction of a quantifier-free formula. -/
def eval (v : ℕ → ℤ) : QF → Prop
  | le t => t.eval v ≤ 0
  | dvd m t => ((m : ℤ) + 1) ∣ t.eval v
  | and φ ψ => φ.eval v ∧ ψ.eval v
  | or φ ψ => φ.eval v ∨ ψ.eval v

/-- A Boolean evaluator of quantifier-free formulas at the zero assignment. -/
def holds0 : QF → Bool
  | le t => decide (t.const ≤ 0)
  | dvd m t => decide (t.const.natAbs % (m + 1) = 0)
  | and φ ψ => φ.holds0 && ψ.holds0
  | or φ ψ => φ.holds0 || ψ.holds0

theorem holds0_iff (φ : QF) : φ.holds0 = true ↔ φ.eval (fun _ => 0) := by
  induction φ with
  | le t => simp only [holds0, eval, Term.eval_zeroEnv, decide_eq_true_eq]
  | dvd m t =>
    simp only [holds0, eval, Term.eval_zeroEnv, decide_eq_true_eq]
    rw [show ((m : ℤ) + 1) = ((m + 1 : ℕ) : ℤ) by push_cast; rfl, Int.natCast_dvd,
      Nat.dvd_iff_mod_eq_zero]
  | and φ ψ ihφ ihψ => simp only [holds0, eval, Bool.and_eq_true, ihφ, ihψ]
  | or φ ψ ihφ ihψ => simp only [holds0, eval, Bool.or_eq_true, ihφ, ihψ]

end QF

namespace PForm

/-- Satisfaction of a Presburger formula under an assignment of the free variables. -/
def eval (v : ℕ → ℤ) : PForm → Prop
  | le t => t.eval v ≤ 0
  | eq t => t.eval v = 0
  | dvd k t => (k : ℤ) ∣ t.eval v
  | not φ => ¬ φ.eval v
  | and φ ψ => φ.eval v ∧ ψ.eval v
  | or φ ψ => φ.eval v ∨ ψ.eval v
  | ex φ => ∃ x : ℤ, φ.eval (cons x v)
  | all φ => ∀ x : ℤ, φ.eval (cons x v)

@[simp] theorem eval_ff (v : ℕ → ℤ) : ¬ ff.eval v := by
  simp only [ff, eval, Term.eval_ofInt]; omega

@[simp] theorem eval_tt (v : ℕ → ℤ) : tt.eval v := by
  simp only [tt, eval, Term.eval_ofInt]; omega

@[simp] theorem eval_imp (v : ℕ → ℤ) (φ ψ : PForm) :
    (imp φ ψ).eval v ↔ (φ.eval v → ψ.eval v) := by
  simp only [imp, eval]; tauto

@[simp] theorem eval_iff (v : ℕ → ℤ) (φ ψ : PForm) :
    (iff φ ψ).eval v ↔ (φ.eval v ↔ ψ.eval v) := by
  simp only [iff, eval_imp, eval]; tauto

@[simp] theorem eval_le' (v : ℕ → ℤ) (s t : Term) : (le' s t).eval v ↔ s.eval v ≤ t.eval v := by
  simp only [le', eval, Term.eval_sub]; omega

@[simp] theorem eval_lt (v : ℕ → ℤ) (s t : Term) : (lt s t).eval v ↔ s.eval v < t.eval v := by
  simp only [lt, eval, Term.eval_sub, Term.eval_add, Term.eval_ofInt]; omega

@[simp] theorem eval_eq' (v : ℕ → ℤ) (s t : Term) : (eq' s t).eval v ↔ s.eval v = t.eval v := by
  simp only [eq', eval, Term.eval_sub]; omega

/-- A formula only depends on the variables below its `bound`. -/
theorem eval_congr (φ : PForm) :
    ∀ {v w : ℕ → ℤ}, (∀ i < φ.bound, v i = w i) → (φ.eval v ↔ φ.eval w) := by
  induction φ with
  | le t | eq t | dvd _ t => intro v w h; simp only [eval, Term.eval_congr t h]
  | not φ ih => intro v w h; simp only [eval, ih h]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ =>
    intro v w h
    simp only [eval, ihφ fun i hi => h i (by simp only [bound]; omega),
      ihψ fun i hi => h i (by simp only [bound]; omega)]
  | ex φ ih | all φ ih =>
    intro v w h
    have key (x : ℤ) : φ.eval (cons x v) ↔ φ.eval (cons x w) :=
      ih fun i hi => by
        cases i with
        | zero => rfl
        | succ i => exact h i (by simp only [bound]; omega)
    simp only [eval, key]

/-- The universal closure `allN n φ` holds iff `φ` holds for every assignment, provided that
`φ` has at most `n` free variables. -/
theorem eval_allN (n : ℕ) (φ : PForm) (hφ : φ.bound ≤ n) (v : ℕ → ℤ) :
    (allN n φ).eval v ↔ ∀ w : ℕ → ℤ, φ.eval w := by
  have key : ∀ (n : ℕ) (v : ℕ → ℤ), (allN n φ).eval v ↔
      ∀ w : ℕ → ℤ, (∀ i, n ≤ i → w i = v (i - n)) → φ.eval w := by
    intro n
    induction n with
    | zero =>
      intro v
      refine ⟨fun h w hw => ?_, fun h => h v fun _ _ => rfl⟩
      obtain rfl : w = v := funext fun i => hw i (Nat.zero_le i)
      exact h
    | succ n ih =>
      intro v
      simp only [allN_succ, eval, ih]
      refine ⟨fun h w hw => h (w n) w fun i hi => ?_, fun h x w hw => h w fun i hi => ?_⟩
      · obtain rfl | hlt := hi.eq_or_lt
        · simp only [Nat.sub_self, cons_zero]
        · rw [show i - n = (i - (n + 1)) + 1 by omega, cons_succ]
          exact hw i hlt
      · rw [hw i (by omega), show i - n = (i - (n + 1)) + 1 by omega, cons_succ]
  rw [key]
  refine ⟨fun h w' => ?_, fun h w _ => h w⟩
  rw [← eval_congr φ (v := fun i => if i < n then w' i else v (i - n)) (fun i hi => by
    simp only [lt_of_lt_of_le hi hφ, ite_true])]
  exact h _ fun i hi => by simp only [Nat.not_lt.2 hi, ite_false]

/-- The natural-number reading of a formula: the same as `eval`, except that the quantifiers range
over `ℕ` (free variables are still integers, so assignments should take values in `ℕ`). -/
def evalNat (v : ℕ → ℤ) : PForm → Prop
  | le t => t.eval v ≤ 0
  | eq t => t.eval v = 0
  | dvd k t => (k : ℤ) ∣ t.eval v
  | not φ => ¬ φ.evalNat v
  | and φ ψ => φ.evalNat v ∧ ψ.evalNat v
  | or φ ψ => φ.evalNat v ∨ ψ.evalNat v
  | ex φ => ∃ n : ℕ, φ.evalNat (cons n v)
  | all φ => ∀ n : ℕ, φ.evalNat (cons n v)

/-- Relativisation of the quantifiers of a formula to the nonnegative integers. -/
def natRel : PForm → PForm
  | le t => le t
  | eq t => eq t
  | dvd k t => dvd k t
  | not φ => not φ.natRel
  | and φ ψ => and φ.natRel ψ.natRel
  | or φ ψ => or φ.natRel ψ.natRel
  | ex φ => ex (and (le (-Term.var 0)) φ.natRel)
  | all φ => all (imp (le (-Term.var 0)) φ.natRel)

/-- Relativising the quantifiers to the nonnegative integers gives the natural-number reading. -/
theorem eval_natRel (φ : PForm) : ∀ v : ℕ → ℤ, φ.natRel.eval v ↔ φ.evalNat v := by
  induction φ with
  | le t | eq t | dvd _ t => intro v; rfl
  | not φ ih => intro v; simp only [natRel, eval, evalNat, ih]
  | and φ ψ ihφ ihψ | or φ ψ ihφ ihψ => intro v; simp only [natRel, eval, evalNat, ihφ, ihψ]
  | ex φ ih =>
    intro v
    simp only [natRel, eval, evalNat, ih, Term.eval_neg, Term.eval_var, cons_zero]
    refine ⟨fun ⟨x, hx, h⟩ => ⟨x.toNat, ?_⟩, fun ⟨n, h⟩ => ⟨n, by omega, h⟩⟩
    rwa [Int.toNat_of_nonneg (by omega)]
  | all φ ih =>
    intro v
    simp only [natRel, eval, eval_imp, evalNat, ih, Term.eval_neg, Term.eval_var, cons_zero]
    refine ⟨fun h n => h n (by omega), fun h x hx => ?_⟩
    have := h x.toNat
    rwa [Int.toNat_of_nonneg (by omega)] at this

end PForm

end Cslib.Presburger
