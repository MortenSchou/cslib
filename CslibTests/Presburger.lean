/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.Presburger.Computable
import Cslib.Computability.Presburger.Decide

/-! # Tests for the Presburger decision procedure

Small sentences decided by evaluating `PForm.valid` in the kernel. -/

namespace CslibTests.Presburger

open Cslib.Presburger Cslib.Presburger.PForm Cslib.Presburger.Term

/-- `∀ x, ∃ y, x = 2 y ∨ x = 2 y + 1`. -/
def parity : PForm :=
  all (ex (or (eq' (var 1) (smul 2 (var 0))) (eq' (var 1) (smul 2 (var 0) + 1))))

/-- `¬ ∃ x, 2 x = 1`. -/
def noHalf : PForm := not (ex (eq' (smul 2 (var 0)) 1))

/-- `∀ x, (∃ y, x = 3 y) → ∃ z, x = 6 z ∨ x = 6 z + 3`. -/
def threeToSix : PForm :=
  all (imp (ex (eq' (var 1) (smul 3 (var 0))))
    (ex (or (eq' (var 1) (smul 6 (var 0))) (eq' (var 1) (smul 6 (var 0) + 3)))))

/-- `∀ x, ∃ y, x = 2 y` is false. -/
def alwaysEven : PForm := all (ex (eq' (var 1) (smul 2 (var 0))))

/-- `∃ x, ∀ y, y ≤ x` is false over `ℤ`. -/
def greatest : PForm := ex (all (le' (var 0) (var 1)))

/-- `∀ x, ∃ y, x < y`. -/
def noGreatest : PForm := all (ex (lt (var 1) (var 0)))

/-- Divisibility atoms: `∀ x, 4 ∣ x → 2 ∣ x`. -/
def fourTwo : PForm := all (imp (dvd 4 (var 0)) (dvd 2 (var 0)))

/-- `∃ x, 1 < x ∧ x < 2` is false over `ℤ`. -/
def noBetween : PForm := ex (and (lt 1 (var 0)) (lt (var 0) 2))

example : parity.valid = true := by decide +kernel
example : noHalf.valid = true := by decide +kernel
example : threeToSix.valid = true := by decide +kernel
example : alwaysEven.valid = false := by decide +kernel
example : greatest.valid = false := by decide +kernel
example : noGreatest.valid = true := by decide +kernel
example : fourTwo.valid = true := by decide +kernel
example : noBetween.valid = false := by decide +kernel
example : (not noBetween).valid = true := by decide +kernel

-- Plain `decide` and `rfl` work as well on small inputs.
example : threeToSix.valid = true := by decide
example : alwaysEven.valid = false := rfl

-- Satisfiability with a free variable: `x₀ + x₀ = 6` is satisfiable, `x₀ + x₀ = 7` is not.
example : (eq' (var 0 + var 0) 6).sat = true := by decide +kernel
example : (eq' (var 0 + var 0) 7).sat = false := by decide +kernel

/-- From a verified computation to a mathematical statement. -/
example : ∀ x : ℤ, ∃ y : ℤ, x = 2 * y ∨ x = 2 * y + 1 := by
  have h := (valid_iff parity).1 (by decide +kernel) (fun _ => 0)
  simpa [parity, PForm.eval, eq', sub_eq_zero] using h

/-- The natural-number reading: every natural number is even or odd. -/
example : parity.natRel.valid = true := by decide +kernel

/-- Over `ℕ`, there is a least element: `∃ x ≥ 0, ∀ y ≥ 0, x ≤ y`. -/
example : (ex (all (le' (var 1) (var 0)))).natRel.valid = true := by decide +kernel

/-- Validity is computable (a statement about all formulas, not about a single one). -/
example : ComputablePred (fun φ : PForm => ∀ v : ℕ → ℤ, φ.eval v) :=
  PForm.computablePred_valid

example : Computable PForm.valid := PForm.computable_valid

end CslibTests.Presburger
