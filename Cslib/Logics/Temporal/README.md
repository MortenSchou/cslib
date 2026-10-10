<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Temporal logics

Temporal logics specify the behaviour of transition systems over time.

- [CTL](CTL): Computation Tree Logic. Formulas (`Basic`), a satisfaction relation over maximal
  paths (`Semantics`), and the fixpoint semantics with its agreement with the path semantics
  (`Denotation`), the embedding of basic modal logic (`Modal`), and `EF`/`AG` as reachability
  (`Reachability`).

## Notation

All notation is scoped. Judgements follow the convention of [Modal](../Modal) and are used with
`open scoped InferenceSystem`:

| Notation | Meaning |
|---|---|
| `⇓CTL[m,s ⊨ φ]` | the state `s` of the model `m` satisfies the CTL formula `φ` |

The operators are in `CTL.Formula` (`EX`, `EF`, `EG`, `AX`, `AF`, `AG`, `E[φ U ψ]`, `A[φ U ψ]`).
The unary operators bind tighter than any connective. In `E[φ U ψ]` and `A[φ U ψ]`, the first
argument needs parentheses if it is a conjunction or weaker.

## Design

- **Models** are modal models for the signature with one unary modality (`Modal.Model` over
  `PFunctor.y`), i.e. a transition relation with a valuation of atoms. The relation need not be total:
  paths are *maximal*, so a path is infinite or ends in a deadlock, a state without successors. This
  is the natural reading for Petri nets, whose markings may deadlock. A maximal path is represented
  as an infinite sequence that stutters at its deadlock. `EX` uses real successors, so deadlocks are
  definable in CTL as `¬EX ⊤`.
- **Operators**: the minimal basis `{⊥, ¬, ∨, EX, E[· U ·], EG}`; other connectives and temporal
  operators are derived. CTL formulas are a separate type, since `EX` must contain `E[· U ·]` and
  `EG`, but `Formula.ofModal` embeds basic modal logic with the same satisfaction. The propositional
  connectives instantiate the operator typeclasses of [Foundations/Logic](../../Foundations/Logic),
  which has no temporal classes yet.

## Plans and notes

- Model checking on finite models, invariance under bisimulation, and the linear-time logic LTL
  are planned.
- CTL\* and the modal μ-calculus, of which CTL and LTL are fragments, would unify the logics.
