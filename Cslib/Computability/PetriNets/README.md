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
| `ReachabilityInstance` | encodable instances of the reachability problem (`ReachInstance`, `Primcodable`; every net with places `Fin d` is represented), the net of an instance, and list-level firing sequences (`runL`) equivalent to reachability |
| `VASSimulation` | the Petri net of a vector addition system, and the lock construction simulating a Petri net by a VAS (`reachable_iff_vas_reach`) |
| `ReachabilityLock` | the lock construction as a primitive recursive translation from instances to coded VAS (`VASCode`) |
| `ReachabilityDecidable` | reachability is decidable: it is recursively enumerable (firing sequences) and so is non-reachability (Presburger inductive invariants of `Computability/VAS`) |

## Plans and notes

- Not yet formalised: the Karp–Miller tree, coloured and inhibitor-arc nets.
