<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
</pre>

# Presburger arithmetic

This directory formalises **Presburger arithmetic** (the first-order theory of the integers with
addition and order) as a *computable syntax* together with a **verified decision procedure**.

Mathlib has the semantic side (`Presburger`-definable sets are semilinear, in
`Mathlib/ModelTheory/Arithmetic/Presburger`) but neither a decision procedure nor a `Primcodable`
syntax, so that statements such as "validity of a Presburger sentence is a computable predicate"
cannot be formulated there. This development provides the syntax and the algorithm.

## Design

- **Purpose-built syntax with de Bruijn indices.** `PForm` has atoms `t ≤ 0`, `t = 0`, `k ∣ t`
  over linear terms `Term` (a constant and a list of coefficients), the connectives `¬ ∧ ∨` and the
  quantifiers `∃ ∀`, which bind the variable `0` of their body. Implication and bi-implication are
  derived.
- **Variables range over `ℤ`.** This is Cooper's classical setting. The natural numbers are
  recovered by relativisation (`PForm.natRel`, `PForm.eval_natRel`).
- **Cooper's quantifier elimination.** `PForm.qe : PForm → QF` produces a quantifier-free
  formula in *positive* normal form (`QF`, where negation is the dualising function `QF.neg`);
  it is correct for all assignments (`PForm.eval_qe`). A single existential quantifier is
  eliminated by `QF.elim`, whose correctness is Cooper's theorem (`QF.eval_cooper`).
- **Total correctness.** The decision procedure `PForm.valid : PForm → Bool` decides validity
  for all assignments of the free variables (`PForm.valid_iff`), and `PForm.sat` decides
  satisfiability. Every function is structurally recursive and so evaluable by the kernel
  (`decide +kernel`).

The procedure is the textbook one and is **not efficient**: the worst case is triply exponential.

## Relation to Mathlib's model theory

`Mathlib/ModelTheory/Arithmetic/Presburger` defines the language `(0, 1, +)` and the semilinear
sets, and `Mathlib/ModelTheory/Encoding` only gives `Encodable` instances for terms and formulas
(`Primcodable` and computability of syntactic operations are listed there as a TODO). Formulas as
`FirstOrder.Language.BoundedFormula` over a language with `≤` and divisibility would reuse
`Realize`, but would lose what the decision procedure needs: a *linear normal form* of terms (the
coefficient of the eliminated variable is read off, not computed by a normalisation that would
itself have to be verified), a total evaluable `Bool`-valued procedure, and a Gödel numbering for
which each operation is primitive recursive. `PForm` is therefore a purpose-built syntax.

## Contents

| File | Contents |
|------|----------|
| `Syntax.lean` | `Term`, `QF`, `PForm` and their derived connectives |
| `Semantics.lean` | assignments, `eval`, `bound`/`eval_congr`, closure, natural-number reading |
| `Cooper.lean` | negation, substitution, coefficient normalisation, Cooper's theorem, `QF.elim` |
| `Decide.lean` | `PForm.qe`, `PForm.valid`, `PForm.sat` and their correctness |
| `PrimrecArith.lean` | primitive recursive integer arithmetic and `gcd`/`lcm` |
| `Encoding.lean` | Gödel numbering (`Denumerable`, hence `Primcodable`, instances) and primitive recursion on `QF` and `PForm` (`primrec_rec`) |
| `Computable.lean` | `PForm.primrec_valid`, `PForm.computable_valid`, `PForm.computablePred_valid` |

Tests are in `CslibTests/Presburger.lean`.
