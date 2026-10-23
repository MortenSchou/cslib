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
  inherited from [Foundations](../../Foundations) and [Logics](../../Logics), including the
  temporal logics CTL and LTL of [Logics/Temporal](../../Logics/Temporal). The marking graph is
  deterministic, so bisimilarity of markings coincides with trace equivalence.
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
| `StateEquation` | incidence, effect of a firing sequence, T-invariants |
| `PlaceInvariants` | weighted token counts preserved by firing, and the bounds they give |
| `Structure` | siphons, traps, and a deadlock-freedom criterion for ordinary nets |
| `Coverability` | coverability and the pumping lemma |
| `CoverabilityBasis` | upward-closed sets of markings have finite bases (Dickson's lemma) |
| `BackwardCoverability` | the backward coverability iteration and its termination |
| `Unboundedness` | a net is unbounded iff some reachable marking reaches a strictly larger one |
| `ExecutableCoverability` | decidable coverability for executable nets |
| `ExecutableBoundedness` | decidable boundedness for executable nets |
| `Labelled` | marking graph with transitions relabelled (used by `Languages/CCS/PetriNet`) |
| [`Search`](../../Foundations/Data/Search.lean) | `searchIter`/`searchNat`: searches that `decide` can evaluate, used by the decision procedures |
| `Automaton` | firing languages of bounded nets are regular |
| `Equivalence` | bisimilarity and HML equivalence of markings |
| `FreeChoice` | free-choice nets and Commoner's theorem: an ordinary free-choice net is live iff every siphon contains a marked trap |
| [`Ranking`](../../Foundations/Data/Set/Ranking.lean) | `exists_rank`: ranking a finite set by successive exits, used for the necessity half of Commoner's theorem |
| `ExecutableStructure` | decidable structural properties (conservative, ordinary, free-choice, siphon-trap) |
| `SoundnessNotions` | workflow nets (`IsWFNet`) and the weak, `k`-, relaxed, lazy and easy notions of soundness |
| `Soundness` | soundness of workflow nets ⟺ short circuit live and bounded |
| [`FiniteClosure`](../../Foundations/Relation/FiniteClosure.lean) | reachability in finite relations is decidable (`ReflTransGen`), used to decide `IsWFNet` |
| `ExecutableForward` | dot notation for executable nets: `N.Bounded M₀`, `N.Sound i o`, … forward to `N.toPetriNet` |
| `ExecutableLanguage` | membership in firing languages of executable nets is decidable |
| `ExecutableReachability` | reachability and deadlock reachability for bounded executable nets |
| `ExecutableSoundnessNotions` | decision procedures for the notions of soundness on bounded executable nets |
| `ExecutableSoundness` | soundness of executable nets is decidable |
| `CTL` | the marking graph as a CTL model; easy and `k`-soundness, liveness and deadlock-freeness as CTL formulas; CTL satisfaction is decidable for bounded executable nets |
| `LTL` | LTL on the maximal firing sequences of a net; LTL model checking is decidable for bounded executable nets |
| `SeriesReduction` | fusion of series transitions (Murata FST), under side conditions: the reduced net is weakly bisimilar to the original, and preserves reachability, deadlock-freedom, liveness, boundedness and soundness of workflow nets; deleting the isolated place gives a workflow net again (`fuseDelete`), so reducing before deciding soundness gives an equivalent question |
| `SeriesPlaceReduction` | fusion of series places (Murata FSP), under side conditions: the same preservation results (liveness needs a producer of the first place), with the merged place holding the tokens of both places |
| `RemovePlace` | deleting a place and restricting markings (`removePlace`, `Marking.drop`); firings, firing sequences and reachability descend to the reduced net; isolated places |
| `Reduction` | Murata's reduction of places: redundant (implicit) places, self-loop places, parallel places and isolated places; deleting a redundant place preserves firing sequences (bisimilarity), deadlocks and liveness, and `N` is bounded iff the reduced net and the deleted place are |
| `ReductionTransition` | fusion of parallel transitions; preserves reachable markings, bisimilarity of the labelled marking graph, liveness, boundedness and deadlocks |
| `SelfLoopTransition` | elimination of self-loop transitions (Murata ESLT): a transition with equal preset and postset can be deleted; the reachable markings, boundedness, safeness and the weak traces (weak bisimilarity, the deleted transition being invisible) are preserved; deadlocks and liveness are preserved under side conditions (the deleted transition is never the only enabled one; it is live whenever the reduced net is), which hold for a live net |
| `ReductionTransitionWF` | deleting one of two parallel transitions preserves and reflects the structure of a workflow net and its soundness, for the same source and sink |
| `ReducesTo` | certificates of reduction: `ReducesTo N M₀ N' M₀'` is a chain of reductions (redundant, self-loop, parallel and isolated places, parallel and self-loop transitions, fusion of series transitions and places) between nets whose places and transitions change along the chain; boundedness, deadlocks and liveness transfer, `k`-boundedness transfers to the reduced net, `reindex` renames places and transitions, and `ReducesWF` transfers workflow structure and soundness through series fusions and the deletion of parallel transitions |
| `ExecutableReduction` | the reductions as operations on executable nets (`removePlace`, `removeTransition`, `fuseDelete`, `dropMarking`, `collapseMarking`) with bridges to the weighted nets; renaming of places and/or transitions (`rename`, `renamePlaces`, `renameTransitions`); decidable side conditions (`IsDrain`, `IsSeries`, `IsSeriesPlace`, `ParallelTransitions`, `ParallelPlaces`, `IsIsolated`, `IsSelfLoopTransition`); certificates for executable nets with one lemma per rule (`fuseDrain`, `selfLoopTransition_of_twin`, …) |
| `ExecutableReducedDecisions` | decide boundedness, liveness, reachable deadlocks and soundness of a net by deciding them for a smaller net, given a hand-built certificate |
| `Rename` | renaming the places and transitions of a net along bijections (`PetriNet.rename`, `Marking.rename`): reachability, boundedness, deadlocks, liveness, workflow structure and soundness are preserved and reflected |
| `ExecutableReductionFin` | reductions of executable nets over `Fin n` places and `Fin m` transitions with the indices renumbered along the explicit bijection `skipEquiv` (`removePlaceFin`, `fuseFin`, …), and the first-instance searches `tryFin`, `tryPair` |
| `ExecutableReductionSearch` | automatic search for reductions: one `try…` function per rule (fusion of a drained place, parallel and self-loop transitions, parallel, self-loop and isolated places) returning a `ReductionStep` with the reduced net and its certificate, `step`, and the iteration `reduce` / `reduceWF` / `reduceBounded` (written once for a `ReductionSystem`) that reach a fixed point |
| `ExecutableAutoDecisions` | decision procedures that reduce the net automatically and then decide on the reduced net: `decideBoundedReduced` (with the extra rule of self-loop transitions), `decideLiveReduced`, `decideDeadlockFreeReduced`, `decideSoundReduced` (and combined versions), and `…Equiv` variants that take bijections with `Fin` types for nets over arbitrary types |
| `Independence` | commuting transitions (an instance of the generic [`LTS.CommutesWith`](../../Foundations/Semantics/LTS/Commutation.lean)), conflicts, and the diamond property of non-conflicting transitions |
| `StubbornSets` | Valmari-style stubborn sets, a structural criterion for them, and deadlock preservation of the reduced marking graph; an instance of the generic [`LTS.reduced`](../../Foundations/Semantics/LTS/Reduction.lean) theory, extended to safety and LTL without next-time in `ExecutableAmple` and `ExecutableAmpleLTL` |
| `ExecutableStubborn` | a computable stubborn selector for executable nets (cheapest enabled seed, least missing place, finset fixpoint), proved closed, and the computed reduced reachable markings |
| `ExecutableAmple` | stubborn sets as ample sets for safety: with visible transitions and a bounded level function as cycle proviso, reachability and invariants of predicates insensitive to invisible transitions are preserved by the reduced graph (finite firing sequences); instances of the generic [`LTS.IsAmple`](../../Foundations/Semantics/LTS/AmpleSets.lean) theory |
| `ExecutableAmpleLTL` | the same selector preserves LTL without next-time on all and on some maximal firing sequence (finite and infinite), for the observed atoms that invisible transitions do not change; an instance of the generic [`LTL.allPaths_reduced_iff`](../../Logics/Temporal/LTL/AmpleSets.lean) |
| `ExecutableAmplePlaces` | the same for LTL over the atoms `k ≤ M p` of the tokens of places, with the transitions that change the observed places as visible transitions; a maximal path of the reduced graph stays in a closed level of the computed reduced reachable markings |
| `ExecutableReducedStubborn` | the two reductions composed: a dead marking is reachable in `N` iff the graph of the reduced net `N'` (a certificate `N.ReducesTo M₀ N' M₀'`, or the automatic search) reduced by the computed stubborn sets reaches one; deadlock reachability and deadlock-freedom are decided on a closed level of that graph, given explicitly or found by search for a bounded net |

## Plans and notes

- Certified reductions: a certificate (`ExecPetriNet.ReducesTo`, `ExecPetriNet.ReducesWF`) can be
  built by hand, rule by rule, with the side conditions of each rule checked by `decide`
  (`ExecutableReducedDecisions`), or found by the automatic search `ExecPetriNet.reduce` /
  `ExecPetriNet.reduceWF` (`ExecutableReductionSearch`, `ExecutableAutoDecisions`). Place
  reductions only shrink the net: they do not change the set of reachable markings, so by
  themselves they do not make `decide` cheaper. They can still enable series fusions, which remove
  markings: deleting the self-loop lock place of a ring of transitions is what makes its transitions
  series-reducible. Soundness is transferred through series fusions and the deletion of parallel
  transitions (`ReductionTransitionWF`); it does not survive the deletion of a redundant place
  (`CslibTests.RedundantPlaceSoundness`: the reduced net is sound, the net is not), and the
  elimination of self-loop transitions is not part of `ReducesWF` (the deleted transition can be
  the only way from one place of its preset to another), so the automatic reduction of workflow
  nets uses fusion of drained places and parallel transitions only.
- Representation of long chains of reductions: each deletion passes to a subtype, and nested
  subtypes strain instance synthesis and `decide` (five nested fusions need
  `synthInstance.maxSize 512`). The search therefore re-indexes after every step, along an explicit
  bijection `{q : Fin n // q ≠ p} ≃ Fin (n - 1)` (`ExecutableReductionFin`), using the constructor
  `reindex` of the certificates, so reduced nets stay over `Fin n'` and chains of a dozen fusions
  are evaluated by `decide +kernel`; the arcs of each reduced net are stored in tables
  (`ExecPetriNet.tabulate`), which makes the reduction of a ring of 80 places three times faster. The rules are tried in a fixed order and the result is a fixed
  point (no rule applies), not necessarily the smallest equivalent net.
- What is searched where. `reduce` (certificate `ReducesTo`, which preserves boundedness,
  deadlocks and liveness): fusion of a drained place that is produced into (`ReducesTo.fuseDrain`,
  which includes Murata's FST and FSP), parallel transitions, parallel, self-loop and isolated
  places, and self-loop transitions that have a twin with the same preset (a decidable condition
  that gives the deadlock and liveness side conditions of `ReducesTo.selfLoopTransition`).
  `reduceBounded` (certificate: the equivalence of boundedness) adds every self-loop transition,
  which preserves boundedness without a side condition; `decideBoundedReduced` uses it. `reduceWF`
  (certificate `ReducesWF`): fusion of a drained place that is neither the source nor the sink, and
  parallel transitions.
  A self-loop transition without a twin can be deleted by a hand-built certificate
  (`ExecPetriNet.ReducesTo.selfLoopTransition`, with its side conditions stated for the
  reachable markings).
- Not searched for: redundant (implicit) places in general, fusion of parallel transitions with
  differing weights, self-loop transitions without a twin outside the boundedness search, and
  unboundedness. Deleting self-loop transitions is not part of `ReducesWF`.

- Combining the structural reduction with stubborn sets (`ExecutableReducedStubborn`). The two
  shrink different things: series fusions remove the positions inside a chain of transitions, and
  stubborn sets remove the interleavings of the independent transitions that are left. Applied
  to `k` independent chains of `len` transitions (`CslibTests.ReducedStubborn`), the net has
  `(len + 1) ^ k` reachable markings, the reduced net `2 ^ k`, and the stubborn-reduced graph of
  the reduced net `k + 1`. Reachable deadlocks are preserved by both, so the composition decides
  deadlock reachability and deadlock-freedom. What each reduction preserves otherwise: boundedness
  and liveness only by the structural reduction (stubborn sets may leave out the firings that a
  liveness or boundedness witness needs); linear temporal properties without next-time over
  observed atoms only by stubborn sets (`ExecutableAmpleLTL`), since the structural reduction
  deletes places. No combined statement is made for those properties.

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets, a decision procedure for generalized soundness (the notion is defined, and
  refuted whenever up-to-`k` soundness fails for some `k`), and a *finite* net encoding of CCS (the
  encoding in `Languages/CCS/PetriNet` has all processes as places).
