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
- **An executable variant.** `ExecPetriNet` uses multisets, so it is computable. It is related to
  `PetriNet` by `ExecPetriNet.toPetriNet` and is used for the verified decision procedures and for
  tests that can be checked by `decide`.
- **Notation.** The scoped notation (`•[N] t`, `M [t⟩[N] M'`, `M ⇝[N] M'`, `⦅a, b⦆`) takes its net
  through the `net%` elaborator, which accepts anything with a `PetriNet.ToPetriNet` instance, so
  that other presentations of nets can use the same notation.

## Contents

| File | Contents |
|------|----------|
| `Elab` | the `net%` elaborator, which lets the notation accept other kinds of nets |
| `Basic` | nets, markings, enabling, firing; token counts; notation |
| `Semantics` | marking graph, reachability, boundedness, safeness, liveness, conservative nets |
| `Executable` | multiset-based nets and a computable firing rule |
| `Monotonicity` | adding tokens preserves firing; boundedness is downward closed |
| `Coverability` | coverability and the pumping lemma |
| `CoverabilityBasis` | upward-closed sets of markings have finite bases (Dickson's lemma) |
| `BackwardCoverability` | the backward coverability iteration and its termination |
| `Unboundedness` | a net is unbounded iff some reachable marking reaches a strictly larger one |
| `ExecutableCoverability` | decidable coverability for executable nets |
| `ExecutableBoundedness` | decidable boundedness for executable nets |
| `Labelled` | marking graph with transitions relabelled (used by `Languages/CCS/PetriNet`) |
| [`Search`](../../Foundations/Data/Search.lean) | `searchIter`/`searchNat`: searches that `decide` can evaluate, used by the decision procedures |

## Plans and notes

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets, and a *finite* net encoding of CCS (the encoding in `Languages/CCS/PetriNet`
  has all processes as places).
