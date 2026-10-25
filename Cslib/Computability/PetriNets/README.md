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
| `CTL` | the marking graph as a CTL model; easy and `k`-soundness, liveness and deadlock-freeness as CTL formulas; CTL satisfaction is decidable for bounded nets |
| `LTL` | LTL on the maximal firing sequences of a net; LTL model checking is decidable for bounded nets |
| `Independence` | commuting transitions (an instance of the generic [`LTS.CommutesWith`](../../Foundations/Semantics/LTS/Commutation.lean)), conflicts, and the diamond property of non-conflicting transitions |
| `StubbornSets` | Valmari-style stubborn sets, a structural criterion for them, and deadlock preservation of the reduced marking graph; an instance of the generic [`LTS.reduced`](../../Foundations/Semantics/LTS/Reduction.lean) theory |

## Plans and notes

- Not yet formalised: reachability for unbounded nets, the Karp–Miller tree, coloured and
  inhibitor-arc nets, and a decision procedure for generalized soundness (the notion is defined, and
  refuted whenever up-to-`k` soundness fails for some `k`).
