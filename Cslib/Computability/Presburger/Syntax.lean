/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.Data.Int.Notation
public import Mathlib.Logic.Function.Iterate

/-! # Syntax of Presburger arithmetic

A purpose-built, computable syntax for Presburger arithmetic over the integers. Variables are
de Bruijn indices: the quantifiers `ex` and `all` bind the variable `0` of their body, and the
variable `i + 1` of the body is the variable `i` of the enclosing context. Free variables are
the natural numbers not captured by a quantifier.

Three types are defined.

* `Term`: linear terms `c + a₀ x₀ + a₁ x₁ + ⋯` with integer coefficients, stored as a constant and
  the list of coefficients `[a₀, a₁, …]`.
* `PForm`: full Presburger formulas, with atoms `t = 0`, `t ≤ 0`, `k ∣ t`, the connectives `¬`,
  `∧`, `∨` and the quantifiers `∃`, `∀` over integer variables.
* `QF`: quantifier-free formulas in a *positive* normal form (atoms `t ≤ 0`, `(m + 1) ∣ t`,
  and `∧`, `∨` only). Negation is not a constructor, it is the dualising function `QF.neg`.
  This is the target type of quantifier elimination (see `Cslib.Computability.Presburger.Cooper`).

Variables range over `ℤ`, which is Cooper's classical setting. The natural numbers are recovered
by relativisation, see `PForm.natRel` in `Cslib.Computability.Presburger.Semantics`.

## Main definitions

- `Presburger.Term`: linear terms, with `Add`, `Neg`, `Sub`, `Term.var`, `Term.const`, `Term.smul`.
- `Presburger.PForm`: Presburger formulas, with the derived `PForm.imp`, `PForm.iff`, `PForm.lt`,
  `PForm.eq'` and so on.
- `Presburger.QF`: positive quantifier-free formulas.
-/

@[expose] public section

namespace Cslib.Presburger

/-- A linear term `const + coeffs₀ * x₀ + coeffs₁ * x₁ + ⋯` over integer variables. Missing
coefficients are `0`. -/
structure Term where
  /-- The constant summand. -/
  const : ℤ
  /-- The coefficients of the variables `x₀, x₁, …`. -/
  coeffs : List ℤ
  deriving DecidableEq, Repr

namespace Term

/-- The constant term `c`. -/
def ofInt (c : ℤ) : Term := ⟨c, []⟩

/-- The term consisting of the variable `x_i`. -/
def var (i : ℕ) : Term := ⟨0, List.replicate i 0 ++ [1]⟩

/-- Pointwise sum of coefficient lists, the shorter list being padded with zeros. -/
def addCoeffs : List ℤ → List ℤ → List ℤ
  | [], bs => bs
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addCoeffs as bs

/-- Scalar multiplication of a term by an integer. -/
def smul (k : ℤ) (t : Term) : Term := ⟨k * t.const, t.coeffs.map (k * ·)⟩

instance : Add Term := ⟨fun s t => ⟨s.const + t.const, addCoeffs s.coeffs t.coeffs⟩⟩

instance : Neg Term := ⟨smul (-1)⟩

instance : Sub Term := ⟨fun s t => s + -t⟩

instance : Zero Term := ⟨ofInt 0⟩

instance : OfNat Term n := ⟨ofInt n⟩

/-- The coefficient of the variable `x₀`. -/
def coef0 (t : Term) : ℤ := t.coeffs.headD 0

/-- The term obtained by removing the variable `x₀` and renumbering the others down by one. -/
def rest (t : Term) : Term := ⟨t.const, t.coeffs.tail⟩

end Term

/-- Quantifier-free Presburger formulas in positive normal form.

The atoms are `t ≤ 0` and `(m + 1) ∣ t`. The modulus is stored as `m` so that it is automatically
positive. -/
inductive QF where
  /-- The atom `t ≤ 0`. -/
  | le (t : Term)
  /-- The atom `(m + 1) ∣ t`. -/
  | dvd (m : ℕ) (t : Term)
  /-- Conjunction. -/
  | and (φ ψ : QF)
  /-- Disjunction. -/
  | or (φ ψ : QF)
  deriving DecidableEq, Repr

/-- Presburger formulas over integer variables with de Bruijn indices. -/
inductive PForm where
  /-- The atom `t ≤ 0`. -/
  | le (t : Term)
  /-- The atom `t = 0`. -/
  | eq (t : Term)
  /-- The atom `k ∣ t`, where `0 ∣ t` means `t = 0`. -/
  | dvd (k : ℕ) (t : Term)
  /-- Negation. -/
  | not (φ : PForm)
  /-- Conjunction. -/
  | and (φ ψ : PForm)
  /-- Disjunction. -/
  | or (φ ψ : PForm)
  /-- Existential quantification, binding the variable `0` of the body. -/
  | ex (φ : PForm)
  /-- Universal quantification, binding the variable `0` of the body. -/
  | all (φ : PForm)
  deriving DecidableEq, Repr

namespace PForm

/-- Falsity. -/
def ff : PForm := le (Term.ofInt 1)

/-- Truth. -/
def tt : PForm := le (Term.ofInt 0)

/-- Implication. -/
def imp (φ ψ : PForm) : PForm := or (not φ) ψ

/-- Bi-implication. -/
def iff (φ ψ : PForm) : PForm := and (imp φ ψ) (imp ψ φ)

/-- The atom `s ≤ t`. -/
def le' (s t : Term) : PForm := le (s - t)

/-- The atom `s < t`. -/
def lt (s t : Term) : PForm := le (s - t + Term.ofInt 1)

/-- The atom `s = t`. -/
def eq' (s t : Term) : PForm := eq (s - t)

/-- The number of variables that a formula can depend on: the free variables are `< bound φ`. -/
def bound : PForm → ℕ
  | le t => t.coeffs.length
  | eq t => t.coeffs.length
  | dvd _ t => t.coeffs.length
  | not φ => φ.bound
  | and φ ψ => max φ.bound ψ.bound
  | or φ ψ => max φ.bound ψ.bound
  | ex φ => φ.bound - 1
  | all φ => φ.bound - 1

/-- The universal closure of the first `n` variables: `∀ xₙ₋₁ … ∀ x₀. φ` (with `x₀` bound
innermost). -/
def allN (n : ℕ) (φ : PForm) : PForm := all^[n] φ

@[simp] theorem allN_zero (φ : PForm) : allN 0 φ = φ := rfl

@[simp] theorem allN_succ (n : ℕ) (φ : PForm) : allN (n + 1) φ = all (allN n φ) :=
  Function.iterate_succ_apply' ..

end PForm

end Cslib.Presburger
