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

## Transformer relations

For a capacity `c`, the transformer relation `x ▷_c y` holds iff there is a run from `c + x` to
`c + y` (Leroux, Section 5). It is periodic and its cone `ℚ≥0 ▷_c` is definable in `FO(ℚ; +, ≤)`
(Corollary 5.16), by way of triples, intraproductions, production graphs, Kirchhoff functions and a
directed Euler lemma. The Euler lemma is proved for arbitrary finite directed multigraphs in
`Cslib/Foundations/Combinatorics/DirectedEuler.lean` (walks as lists of edges, `Cslib.DiMultigraph.IsWalk`,
`Cslib.DiMultigraph.exists_closed_walk_count_eq`), since Mathlib has Eulerian trails only for simple graphs.

| File | Contents |
|------|----------|
| `Euler.lean` | `ProdGraph` (its paths are the walks of the multigraph of its transitions), strong connectivity, Kirchhoff functions, displacement, `relR`; the directed Euler lemma `ProdGraph.euler_lemma`; linearity of Kirchhoff functions and displacement; definability of `relR` (via `RatDefinable.proj`) |
| `Transformer.lean` | `VAS.transSet`, `VAS.relVecHom`, periodicity (Lemma 5.2), triples `VAS.Triple` with `runs`, `Q`, `bounded`, `intraprod`; Lemmas 5.5, 5.6, 5.7 |
| `ProdGraphFinite.lean` | König's lemma for prefix-closed sets of words and the finiteness of classes of deterministic graphs with incomparable states |
| `TransformerGraph.lean` | The production graph `Triple.graph`; Corollaries 5.9–5.12 (`proj_add_intraprod`, `graph_stronglyConnected`, `graph_states_incomparable`, `finite_prodGraphs`) and `graph_finite` |
| `TransformerRel.lean` | `Triple.R`, Lemma 5.14 (`xy_mem_R`), `R_definable`, `finite_R` |
| `TransformerCone.lean` | Lemma 5.15 (`R_subset_ratCone`), by Euler's lemma and a pumping argument |
| `TransformerAsymp.lean` | `ratCone_transSet_eq` and `ratDefinable_ratCone_transSet` (Corollary 5.16) |

## Almost semilinear reachability sets and Presburger separators

| File | Contents |
|------|----------|
| `RunTrans.lean` | The transformer relation `π▷` along a run (`Run.trans`), its encoding `relVecSet`, and `runTrans_asympDefinable` by induction on the run |
| `ReachInter.lean` | A finite basis for partially well-ordered sets; `reach_inter_linear` (Lemma 6.1) |
| `PostInter.lean` | Closure properties of `AlmostSemilinear`; `almostSemilinear_reach_inter`, `reach_isAlmostSemilinear` (POPL Thm 9.1), `almostSemilinear_post_inter` (Corollary 6.3) |
| `Separators.lean` | `separator_improve` (Lemma 9.1), `separator_complete`, `exists_semilinear_invariant` (Theorem 9.2), `VAS.not_reach_iff`: `y` is not reachable from `x` iff some semilinear set contains `x`, omits `y` and is closed under moves |

Some statements differ from the paper in minor ways: `ProdGraph` has a `WellFormed` predicate
(transitions go between states), which `euler_lemma` assumes, since the lemma is false without it;
several statements take `[Finite ι]` (or `[Fintype ι]`), a `DecidableEq` instance on the transitions
of a production graph (for Parikh images), or use `classical`.
