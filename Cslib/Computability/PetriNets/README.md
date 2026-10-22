<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
</pre>

# Petri nets

This directory formalises **place/transition (P/T) Petri nets** and their basic theory.

## Design

- **Weighted arcs.** A net has a type of places and a type of transitions, and two weight maps
  `pre` and `post` from transitions to markings. Markings are finitely supported functions
  `Place →₀ ℕ`, so places and transitions can be arbitrary types, finite or infinite.
- **Semantics through `LTS`.** The marking graph of a net is an `LTS` whose labels are the
  transitions (`PetriNet.lts`). Reachability, bisimilarity, trace equivalence, and HML are therefore
  inherited from [Foundations](../../Foundations) and [Logics](../../Logics). The marking graph is
  deterministic.
- **Notation.** The scoped notation (`•[N] t`, `M [t⟩[N] M'`, `M ⇝[N] M'`, `⦅a, b⦆`) takes its net
  through the `net%` elaborator, which accepts anything with a `PetriNet.ToPetriNet` instance, so
  that other presentations of nets can use the same notation.

## Contents

| File | Contents |
|------|----------|
| `Elab` | the `net%` elaborator, which lets the notation accept other kinds of nets |
| `Basic` | nets, markings, enabling, firing; token counts; notation |
| `Semantics` | marking graph, reachability, boundedness, safeness, liveness, conservative nets |
| `StateEquation` | incidence, effect and Parikh vector of a firing sequence, T-invariants |
| `PlaceInvariants` | weighted token counts preserved by firing, and the bounds they give |
| `Structure` | siphons, traps, and a deadlock-freedom criterion for ordinary nets |
| `ReachabilityConditions` | the state equation is sufficient for reachability in flow-acyclic nets (Murata), with a counterexample for nets with cycles; an a-priori bound on solutions, which makes reachability a finite search for flow-acyclic nets whose transitions have input places |
| `ConflictFree` | conflict-free nets are persistent, firing sequences inside a firable vector can be completed (so greedy firing never backtracks), and reachability is characterised by the state equation and unmarked siphons (Landweber–Robertson) |

## Plans and notes

- Reachability for finite flow-acyclic nets. Done: if every transition has an input place, every
  nonnegative solution of the state equation fires `t` at most `B t` times for a bound `B` computed
  by recursion along `Feeds` (`FlowAcyclic.exists_bound`), so reachability from `M₀` is solvability
  of the state equation in a fixed finite set of vectors (`FlowAcyclic.exists_finite_search`).
  This is stated as a finite search rather than as a `Decidable` instance, which would be vacuous
  here since the `Finsupp` operations are noncomputable. Open: nets with transitions without input
  places, where solutions are not bounded (a source feeding a sink can be repeated arbitrarily) and
  one must bound minimal solutions instead.

- Conflict-free nets (`ConflictFree`): persistence, the completion theorem, the "greedy firing never
  backtracks" theorem and the Landweber–Robertson characterisation are proved, the latter for nets
  whose arcs into transitions have weight at most one (`ConflictFree.firable_iff`,
  `ConflictFree.reachable_iff_siphons`); the weight bound is needed
  (`Example.weighted_not_firable`). Open: a weighted version of the siphon condition.

- Not yet formalised: decidability of reachability for unbounded nets (only the state-equation
  conditions are proved), the Karp–Miller tree, coloured and inhibitor-arc nets.
