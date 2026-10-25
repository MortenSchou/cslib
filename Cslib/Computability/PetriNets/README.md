<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
</pre>

# Petri nets

This directory formalises **place/transition (P/T) Petri nets** and their basic theory.

## Design

- **Multisets.** A net has a type of places and a type of transitions, and two maps `pre` and
  `post` from transitions to multisets of places; the multiplicity of a place is the arc weight.
  Markings are multisets of places, as in the Petri net literature, so places and transitions can
  be arbitrary types, finite or infinite, and markings are written `{a, b, b}`.
- **One definition, computable.** Multisets are computable as soon as places have decidable
  equality, so the same `PetriNet` is used for the theory and for tests checked by `decide`.
  Notions that do not count tokens (enabling, firing, reachability, boundedness, …) do not assume
  decidable equality of places.
- **Semantics through `LTS`.** The marking graph of a net is an `LTS` whose labels are the
  transitions (`PetriNet.lts`). Reachability, bisimilarity, trace equivalence, and HML are therefore
  inherited from [Foundations](../../Foundations) and [Logics](../../Logics). The marking graph is
  deterministic.
- **Notation.** The scoped notation `•[N] t`, `t •[N]`, `M [t⟩[N]`, `M [t⟩[N] M'` and `M ⇝[N] M'`.

## Contents

| File | Contents |
|------|----------|
| `Basic` | nets, markings, enabling, firing, the computable firing rule; notation |
| `Semantics` | marking graph, reachability, boundedness, safeness, liveness, conservative nets |
| `StateEquation` | incidence, effect and firing count vectors of firing sequences, T-invariants |
| `PlaceInvariants` | weighted token counts preserved by firing, and the bounds they give |
| `Structure` | siphons, traps, and a deadlock-freedom criterion for ordinary nets |
| `ReachabilityConditions` | the state equation is sufficient for reachability in flow-acyclic nets (Murata), with a counterexample for nets with cycles; an a-priori bound on solutions, which makes reachability a finite search for flow-acyclic nets whose transitions have input places |
| `ConflictFree` | conflict-free nets are persistent, firing sequences inside a firable vector can be completed (so greedy firing never backtracks), and reachability is characterised by the state equation and unmarked siphons (Landweber–Robertson) |

## Plans and notes

- Firing count vectors (Parikh vectors) are multisets of transitions; the firing count vector of a
  firing sequence `ts` is `(ts : Multiset Transition)`. The state equation for a firing count
  vector `σ` is stated on multisets, `M + Σ_{t ∈ σ} pre t = M₀ + Σ_{t ∈ σ} post t`, so it needs no
  integers and no decidable equality.

- Reachability for finite flow-acyclic nets. Done: if every transition has an input place, every
  solution of the state equation is below a fixed firing count vector `B` obtained by recursion
  along `Feeds` (`FlowAcyclic.exists_bound`), so reachability from `M₀` is solvability of the
  state equation by a sub-multiset of `B` (`FlowAcyclic.exists_finite_search`). The bound is only
  shown to exist, so this is not yet a `Decidable` instance. Open: nets with transitions without
  input places, where solutions are not bounded (a source feeding a sink can be repeated
  arbitrarily) and one must bound minimal solutions instead.

- Conflict-free nets (`ConflictFree`): persistence, the completion theorem, the "greedy firing never
  backtracks" theorem and the Landweber–Robertson characterisation are proved, the latter for nets
  whose arcs into transitions have weight at most one, that is, whose presets have no duplicates
  (`ConflictFree.firable_iff`, `ConflictFree.reachable_iff_siphons`); the weight bound is needed
  (`Example.weighted_not_firable`). Open: a weighted version of the siphon condition.

- Not yet formalised: decidability of reachability for unbounded nets (only the state-equation
  conditions are proved), the Karp–Miller tree, coloured and inhibitor-arc nets.
