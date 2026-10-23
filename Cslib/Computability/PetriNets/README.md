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
| `SeriesReduction` | fusion of series transitions (Murata FST), under side conditions: the reduced net is weakly bisimilar to the original, and preserves reachability, deadlock-freedom, liveness, boundedness and soundness of workflow nets; deleting the isolated place gives a workflow net again (`fuseDelete`), so reducing before deciding soundness gives an equivalent question |
| `SeriesPlaceReduction` | fusion of series places (Murata FSP), under side conditions: the same preservation results (liveness needs a producer of the first place), with the merged place holding the tokens of both places |
| `RemovePlace` | deleting a place and restricting markings (`removePlace`, `Marking.drop`); firings, firing sequences and reachability descend to the reduced net; isolated places |
| `Reduction` | Murata's reduction of places: redundant (implicit) places, self-loop places, parallel places and isolated places; deleting a redundant place preserves firing sequences (bisimilarity), deadlocks and liveness, and `N` is bounded iff the reduced net and the deleted place are |
| `ReductionTransition` | fusion of parallel transitions; preserves reachable markings, bisimilarity of the labelled marking graph, liveness, boundedness and deadlocks |
| `SelfLoopTransition` | elimination of self-loop transitions (Murata ESLT): a transition with equal preset and postset can be deleted; the reachable markings, boundedness, safeness and the weak traces (weak bisimilarity, the deleted transition being invisible) are preserved; deadlocks and liveness are preserved under side conditions (the deleted transition is never the only enabled one; it is live whenever the reduced net is), which hold for a live net |
| `ReductionTransitionWF` | deleting one of two parallel transitions preserves and reflects the structure of a workflow net and its soundness, for the same source and sink |

## Plans and notes

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets, a decision procedure for generalized soundness (the notion is defined, and
  refuted whenever up-to-`k` soundness fails for some `k`), and a *finite* net encoding of CCS (the
  encoding in `Languages/CCS/PetriNet` has all processes as places).
