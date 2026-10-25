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
| `Monotonicity` | adding tokens preserves firing (`StronglyMonotone` for every net); boundedness is downward closed |
| `Coverability` | coverability (`WSTS.Coverable` of the marking graph) and the pumping lemma; Dickson's lemma for multisets |
| `CoverabilityBasis` | upward-closed sets of markings have finite bases |
| `BackwardCoverability` | the backward coverability iteration and its termination (specialisations of the generic `WSTS` ones) |
| `Unboundedness` | a net is unbounded iff some reachable marking reaches a strictly larger one (the König half is the generic `WSTS.exists_pump_of_infinite_reachable`) |
| [`WSTS`](WSTS.lean) | nets as well-structured transition systems; `instWSTS` over finitely many places, and the characterisation of infinite firing sequences via [`Computability/WSTS`](../WSTS) |

## Plans and notes

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets.
