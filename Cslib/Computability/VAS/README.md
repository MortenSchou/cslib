<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
</pre>

# Vector addition systems

This directory formalises vector addition systems (VAS) and the combinatorics needed for Leroux's
proof that reachability of VAS and Petri nets is decidable, by Presburger inductive invariants: if
`y` is not reachable from `x`, then there is a semilinear set containing `x`, omitting `y`, and
closed under moves.

Definitions are in `Defs.lean`. Reachability, invariants and separators are defined there; the
remaining files are listed below. A VAS gives a labelled transition system (`VAS.lts`, labelled by
actions), and `VAS.Reach` is its reachability relation (`VAS.reach_iff_canReach`); it is kept as a
`Relation.ReflTransGen` of moves because that is the form the proofs use. Runs are chains of
configurations in the sense of `List.IsChainFromTo`.

## Basic theory and runs

| File | Contents |
|------|----------|
| `Basic.lean` | Monotony, `post`/`pre` as least invariants, soundness of inductive invariants, separators with empty domain |
| `Run.lean` | `VAS.Run` (a non-empty chain of configurations) with `src`, `tgt`, `dir`; reachability is the existence of a run; runs through a configuration or a move (via `List.IsChainFromTo`); `relVec` |
| `WellOrder.lean` | Runs as words, the Higman order `WordLE`, the decomposition order `Embeds`, their well-quasi-ordering, and `RunLE` on runs with directions in a periodic translate |

## Periodic sets, dimension and linearizations

| File | Contents |
|------|----------|
| `Periodic.lean` | `IsPeriodic` (with `IsPeriodic.toAddSubmonoid`, hence closure under multiples and finite sums), `ratVec`, `ratCone` |
| `AsympDefinable.lean` | `AsympDefinable`; finitely generated periodic sets are asymptotically definable; closure under intersection (Lemma 6.2) and composition of relations (Lemma 5.1) |
| `Dimension.lean` | `DimLE`, `dim` (valued in `WithBot ℕ`, characterised by `dim_le_iff`), its behaviour under inclusion, unions and translation; a periodic set covered by finitely many affine spaces lies in one of them (Lemma 7.3); `dim_periodic` (Lemma 7.4) |
| `Linearization.lean` | `lin`, `IsLinearization`; linearizations are semilinear; `exists_linear_subset_dim`; `lin_lemma_8_3`; the dimension drop `dim_inter_linearizations_lt` (Corollary 8.4) |
