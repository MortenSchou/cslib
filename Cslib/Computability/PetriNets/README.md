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
  equality, so the same `PetriNet` is used for the theory, for the verified decision procedures
  (the files in `Decision/`) and for tests checked by `decide`.
  Notions that do not count tokens (enabling, firing, reachability, boundedness, …) do not assume
  decidable equality of places.
- **Semantics through `LTS`.** The marking graph of a net is an `LTS` whose labels are the
  transitions (`PetriNet.lts`). Reachability, bisimilarity, trace equivalence, and HML are therefore
  inherited from [Foundations](../../Foundations) and [Logics](../../Logics), including the
  temporal logics CTL and LTL of [Logics/Temporal](../../Logics/Temporal). The marking graph is
  deterministic, so bisimilarity of markings coincides with trace equivalence.
- **Notation.** The scoped notation `•[N] t`, `t •[N]`, `M [t⟩[N]`, `M [t⟩[N] M'` and `M ⇝[N] M'`.

## Contents

| File | Contents |
|------|----------|
| `Basic` | nets, markings, enabling, firing, the computable firing rule; notation |
| `Semantics` | marking graph, reachability, boundedness, safeness, liveness, conservative nets |
| `Monotonicity` | adding tokens preserves firing (`StronglyMonotone` for every net); boundedness is downward closed |
| `StateEquation` | incidence, effect of a firing sequence, T-invariants |
| `PlaceInvariants` | weighted token counts preserved by firing, and the bounds they give |
| `Structure` | siphons, traps, and a deadlock-freedom criterion for ordinary nets |
| `Coverability` | coverability (`WSTS.Coverable` of the marking graph) and the pumping lemma; Dickson's lemma for multisets |
| `CoverabilityBasis` | upward-closed sets of markings have finite bases |
| `BackwardCoverability` | the backward coverability iteration and its termination (specialisations of the generic `WSTS` ones) |
| `Unboundedness` | a net is unbounded iff some reachable marking reaches a strictly larger one (the König half is the generic `WSTS.exists_pump_of_infinite_reachable`) |
| [`WSTS`](WSTS.lean) | nets as well-structured transition systems; `instWSTS` over finitely many places, and the characterisation of infinite firing sequences via [`Computability/WSTS`](../WSTS) |
| `Decision/Coverability` | decidable coverability for nets over finitely many places: the net-specific predecessor basis `•[N] t + (b - t •[N])` fed to the generic `WSTS.decidableCoverable` |
| `Decision/Boundedness` | decidable boundedness for nets over finitely many places |
| `Labelled` | marking graph with transitions relabelled (used by `Languages/CCS/PetriNet`) |
| [`Search`](../../Foundations/Data/Search.lean) | `searchIter`/`searchNat`: searches that `decide` can evaluate, used by the decision procedures |
| `FreeChoice` | free-choice nets and Commoner's theorem: an ordinary free-choice net is live iff every siphon contains a marked trap |
| [`Ranking`](../../Foundations/Data/Set/Ranking.lean) | `exists_rank`: ranking a finite set by successive exits, used for the necessity half of Commoner's theorem |
| `Decision/Structure` | decidable structural properties (conservative, ordinary, free-choice, siphon-trap) |
| `SoundnessNotions` | workflow nets (`IsWFNet`) and the weak, `k`-, relaxed, lazy and easy notions of soundness |
| `Soundness` | soundness of workflow nets ⟺ short circuit live and bounded |
| `Automaton` | firing languages of bounded nets are regular |
| `Equivalence` | bisimilarity and HML equivalence of markings |
| [`FiniteClosure`](../../Foundations/Relation/FiniteClosure.lean) | reachability in finite relations is decidable (`ReflTransGen`), used to decide `IsWFNet` |
| `Decision/Language` | membership in firing languages of nets is decidable |
| `Decision/Reachability` | reachability and deadlock reachability for bounded nets |
| `Decision/SoundnessNotions` | decision procedures for the notions of soundness on bounded nets |
| `Decision/Soundness` | soundness of nets is decidable |
| `CTL` | the marking graph as a CTL model; easy and `k`-soundness, liveness and deadlock-freeness as CTL formulas; CTL satisfaction, hence liveness (`decidableLive`), is decidable for bounded nets |
| `LTL` | LTL on the maximal firing sequences of a net; LTL model checking is decidable for bounded nets |
| `SeriesReduction` | fusion of series transitions (Murata FST), under side conditions: the reduced net is weakly bisimilar to the original, and preserves reachability, deadlock-freedom, liveness, boundedness and soundness of workflow nets; deleting the isolated place gives a workflow net again (`fuseDelete`), so reducing before deciding soundness gives an equivalent question. The reduction (`fuse`, `fuseDelete`, `collapse`) is computable and its side conditions are decidable |
| `SeriesPlaceReduction` | fusion of series places (Murata FSP), under side conditions: the same preservation results (liveness needs a producer of the first place), with the merged place holding the tokens of both places |
| `RemovePlace` | deleting a place and restricting markings (`removePlace`, `Marking.drop`, both computable); firings, firing sequences and reachability descend to the reduced net; isolated places |
| `Reduction` | Murata's reduction of places: redundant (implicit) places, self-loop places, parallel places and isolated places; deleting a redundant place preserves firing sequences (bisimilarity), deadlocks and liveness, and `N` is bounded iff the reduced net and the deleted place are |
| `ReductionTransition` | fusion of parallel transitions; preserves reachable markings, bisimilarity of the labelled marking graph, liveness, boundedness and deadlocks |
| `SelfLoopTransition` | elimination of self-loop transitions (Murata ESLT): a transition with equal preset and postset can be deleted; the reachable markings, boundedness, safeness and the weak traces (weak bisimilarity, the deleted transition being invisible) are preserved; deadlocks and liveness are preserved under side conditions (the deleted transition is never the only enabled one; it is live whenever the reduced net is), which hold for a live net |
| `ReductionTransitionWF` | deleting one of two parallel transitions preserves and reflects the structure of a workflow net and its soundness, for the same source and sink |
| `ReducesTo` | certificates of reduction: `ReducesTo N M₀ N' M₀'` is a chain of reductions (redundant, self-loop, parallel and isolated places, parallel and self-loop transitions, fusion of series transitions and places) between nets whose places and transitions change along the chain; boundedness, deadlocks and liveness transfer, `k`-boundedness transfers to the reduced net, `reindex` renames places and transitions, and `ReducesWF` transfers workflow structure and soundness through series fusions and the deletion of parallel transitions |
| `Decision/Reduced` | decide boundedness, liveness, reachable deadlocks and soundness of a net by deciding them for a smaller net, given a hand-built certificate (`ReducesTo`, `ReducesWF`) |
| `Rename` | renaming the places and transitions of a net along bijections (`PetriNet.rename`, computable; markings are renamed by `Multiset.map`): reachability, boundedness, deadlocks, liveness, workflow structure and soundness are preserved and reflected |
| `Decision/ReductionFin` | reductions of nets over `Fin n` places and `Fin m` transitions with the indices renumbered along the explicit bijection `skipEquiv` (`removePlaceFin`, `fuseFin`, …), and the first-instance searches `tryFin`, `tryPair` |
| `Decision/ReductionSearch` | automatic search for reductions: one `try…` function per rule (fusion of a drained place, parallel and self-loop transitions, parallel, self-loop and isolated places) returning a `ReductionStep` with the reduced net and its certificate, `step`, and the iteration `reduce` / `reduceWF` / `reduceBounded` (written once for a `ReductionSystem`) that reach a fixed point |
| `Decision/AutoReduction` | decision procedures that reduce the net automatically and then decide on the reduced net: `decideBoundedReduced` (with the extra rule of self-loop transitions), `decideLiveReduced`, `decideDeadlockFreeReduced`, `decideSoundReduced` (and combined versions), and `…Equiv` variants that take bijections with `Fin` types for nets over arbitrary types |

## Plans and notes

- Certified reductions: a certificate (`PetriNet.ReducesTo`, `PetriNet.ReducesWF`) chains
  reductions rule by rule, with the side conditions of each rule stated for the nets and checked
  by `decide` (`Decision/Reduced`), or is found by the automatic search `PetriNet.reduce` /
  `PetriNet.reduceWF` (`Decision/ReductionSearch`, `Decision/AutoReduction`). Place reductions
  only shrink the net: they do not change the set of reachable markings, so by themselves they do
  not make `decide` cheaper. They can still enable series fusions, which remove markings: deleting
  the self-loop lock place of a ring of transitions is what makes its transitions
  series-reducible. Soundness is transferred through series fusions and the deletion of parallel
  transitions (`ReductionTransitionWF`); it does not survive the deletion of a redundant place
  (`CslibTests.RedundantPlaceSoundness`: the reduced net is sound, the net is not), and the
  elimination of self-loop transitions is not part of `ReducesWF` (the deleted transition can be
  the only way from one place of its preset to another), so the automatic reduction of workflow
  nets uses fusion of drained places and parallel transitions only.
- Representation of long chains of reductions: each deletion passes to a subtype, and nested
  subtypes strain instance synthesis and `decide` (five nested fusions need
  `synthInstance.maxSize 512`). The search therefore re-indexes after every step, along an explicit
  bijection `{q : Fin n // q ≠ p} ≃ Fin (n - 1)` (`Decision/ReductionFin`), using the constructor
  `reindex` of the certificates, so reduced nets stay over `Fin n'` and chains of a dozen fusions
  are evaluated by `decide +kernel`; the arcs of each reduced net are stored in tables
  (`PetriNet.tabulate`), so that they are computed once per step. The rules are tried in a fixed
  order and the result is a fixed point (no rule applies), not necessarily the smallest equivalent
  net.
- What is searched where. `reduce` (certificate `ReducesTo`, which preserves boundedness,
  deadlocks and liveness): fusion of a drained place that is produced into (`ReducesTo.fuseDrain`,
  which includes Murata's FST and FSP), parallel transitions, parallel, self-loop and isolated
  places, and self-loop transitions that have a twin with the same preset (a decidable condition
  that gives the deadlock and liveness side conditions of `ReducesTo.selfLoopTransition`).
  `reduceBounded` (certificate: the equivalence of boundedness) adds every self-loop transition,
  which preserves boundedness without a side condition; `decideBoundedReduced` uses it. `reduceWF`
  (certificate `ReducesWF`): fusion of a drained place that is neither the source nor the sink, and
  parallel transitions. A self-loop transition without a twin can be deleted by a hand-built
  certificate (`PetriNet.ReducesTo.selfLoopTransition`, with its side conditions stated for the
  reachable markings).
- Not searched for: redundant (implicit) places in general, fusion of parallel transitions with
  differing weights, self-loop transitions without a twin outside the boundedness search, and
  unboundedness. Deleting self-loop transitions is not part of `ReducesWF`.

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets, a decision procedure for generalized soundness (the notion is defined, and
  refuted whenever up-to-`k` soundness fails for some `k`), and a *finite* net encoding of CCS (the
  encoding in `Languages/CCS/PetriNet` has all processes as places).
