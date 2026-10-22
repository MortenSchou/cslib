/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Presburger.Cooper

/-! # A decision procedure for Presburger arithmetic

Full quantifier elimination `PForm.qe` and the resulting decision procedure `PForm.valid`.

**Design decision.** We use Cooper's quantifier elimination over `ℤ` rather than the
automata-theoretic method (Büchi, Wolper, Boigelot), for three reasons: the algorithm is a
structurally recursive function on a purpose-built syntax, so it is evaluable by the kernel
(`decide +kernel`) and amenable to `Primrec` proofs; the correctness proof is elementary and
self-contained (see `Cslib.Computability.Presburger.Cooper`); and the automata method would need
determinisation and complementation of Büchi-style automata over the binary encoding of
integers, which the repository's automata library does not provide for this purpose.

`qe` eliminates quantifiers innermost-first: `∃ φ` becomes `QF.elim (qe φ)` and `∀ φ` becomes
`¬ ∃ ¬`. The result is a positive quantifier-free formula, whose truth at the zero assignment is
computed by `QF.holds0`.

## Complexity

Cooper's algorithm is, in the worst case, triply exponential in the size of the formula (one
exponential per quantifier alternation in the number of terms produced, and another in the size of
the numbers). The implementation does not simplify intermediate formulas, so it is only suited to
small sentences. It is a *specification* of a decision procedure with a total-correctness proof,
not an efficient solver.

## Main definitions

- `Presburger.PForm.qe`: quantifier elimination.
- `Presburger.PForm.valid`: decide whether a formula holds for all assignments.
- `Presburger.PForm.sat`: decide whether a formula holds for some assignment.

## Main statements

- `Presburger.PForm.eval_qe`: `φ.qe.eval v ↔ φ.eval v`.
- `Presburger.PForm.valid_iff`: `φ.valid = true ↔ ∀ v, φ.eval v`.
- `Presburger.PForm.sat_iff`: `φ.sat = true ↔ ∃ v, φ.eval v`.
-/

@[expose] public section

namespace Cslib.Presburger

namespace PForm

/-- Quantifier elimination: a quantifier-free formula equivalent to `φ`. -/
def qe : PForm → QF
  | le t => QF.le t
  | eq t => QF.and (QF.le t) (QF.le (-t))
  | dvd 0 t => QF.and (QF.le t) (QF.le (-t))
  | dvd (k + 1) t => QF.dvd k t
  | not φ => φ.qe.neg
  | and φ ψ => QF.and φ.qe ψ.qe
  | or φ ψ => QF.or φ.qe ψ.qe
  | ex φ => φ.qe.elim
  | all φ => φ.qe.neg.elim.neg

/-- **Soundness and completeness of quantifier elimination.** -/
theorem eval_qe (φ : PForm) : ∀ v : ℕ → ℤ, φ.qe.eval v ↔ φ.eval v := by
  induction φ with
  | le t => intro v; rfl
  | eq t =>
    intro v
    simp only [qe, QF.eval, eval, Term.eval_neg]
    omega
  | dvd k t =>
    intro v
    cases k with
    | zero =>
      simp only [qe, QF.eval, eval, Term.eval_neg, Nat.cast_zero, zero_dvd_iff]
      omega
    | succ k => simp only [qe, QF.eval, eval, Nat.cast_add, Nat.cast_one]
  | not φ ih => intro v; simp only [qe, QF.eval_neg, eval, ih]
  | and φ ψ ihφ ihψ => intro v; simp only [qe, QF.eval, eval, ihφ, ihψ]
  | or φ ψ ihφ ihψ => intro v; simp only [qe, QF.eval, eval, ihφ, ihψ]
  | ex φ ih => intro v; simp only [qe, QF.eval_elim, eval, ih]
  | all φ ih =>
    intro v
    simp only [qe, QF.eval_neg, QF.eval_elim, eval, ih]
    exact ⟨fun h x => by_contra fun hx => h ⟨x, hx⟩, fun h ⟨x, hx⟩ => hx (h x)⟩

/-- Decide whether `φ` holds for every assignment of its free variables: eliminate the quantifiers
of the universal closure and evaluate the resulting closed quantifier-free formula. -/
def valid (φ : PForm) : Bool := (allN φ.bound φ).qe.holds0

/-- **Decision procedure.** `valid φ` decides whether `φ` is true under all assignments; in
particular, it decides truth of sentences. -/
theorem valid_iff (φ : PForm) : φ.valid = true ↔ ∀ v : ℕ → ℤ, φ.eval v := by
  rw [valid, QF.holds0_iff, eval_qe, eval_allN _ φ le_rfl]

/-- Decide whether `φ` is true under some assignment of its free variables. -/
def sat (φ : PForm) : Bool := !(not φ).valid

theorem sat_iff (φ : PForm) : φ.sat = true ↔ ∃ v : ℕ → ℤ, φ.eval v := by
  rw [sat, Bool.not_eq_true', ← Bool.not_eq_true, valid_iff]
  simp [eval]

end PForm

end Cslib.Presburger
