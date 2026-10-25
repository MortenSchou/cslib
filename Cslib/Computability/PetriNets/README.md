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
| `StateEquation` | incidence, effect of a firing sequence, T-invariants |
| `PlaceInvariants` | weighted token counts preserved by firing, and the bounds they give |
| `Structure` | siphons, traps, and a deadlock-freedom criterion for ordinary nets |

## Plans and notes

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets.
