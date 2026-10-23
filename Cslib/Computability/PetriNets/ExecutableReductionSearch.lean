/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableReductionFin

/-! # Searching for reductions

Given an executable net over `Fin n` places and `Fin m` transitions, the functions here search for a
reduction that applies, and apply it. The result is again a net over `Fin n'` and `Fin m'`, together
with a certificate (`ExecPetriNet.ReducesTo` or `ExecPetriNet.ReducesWF`) that it is a reduction of
the original net. Iterating the search (`ExecPetriNet.reduce`) reduces a net until no rule applies.

## Design: re-index after every step

Every step deletes a place or a transition and renumbers the rest
(`Cslib.Computability.PetriNets.ExecutableReductionFin`), so types stay `Fin n'` for a numeral `n'`
whatever the number of steps, and `decide +kernel` can evaluate chains of reductions. The
renumbering is the `reindex` rule of the certificates
(`Cslib.Computability.PetriNets.Rename`), which preserves every property.

A batch alternative (compute the set of removable places and transitions, then apply one
restricted net) would give one subtype, but the removable places depend on the earlier deletions
(a fusion changes the arcs of the other places), so it is not equivalent to iterating.

## Search

A `ReductionStep` records the reduced net, its initial marking (or its source and sink), the
certificate, and that the number of places plus transitions has strictly decreased. Each rule has a
decidable side condition, a predicate on `Fin`s, and a search function that finds the first
instance (`tryFin`, `tryPair`) and builds the step:

- `tryFuseDrain`: fuse a place with the transition that drains it, and delete the place
  (`ReducesTo.fuseDrain`). This covers Murata's fusion of series transitions and of series places.
- `tryRemoveParallelTransition`: delete one of two parallel transitions.
- `tryRemoveSelfLoopTransition`: delete a self-loop transition that has a twin with the same
  preset (`ReducesTo.selfLoopTransition_of_twin`). Elimination of an arbitrary self-loop transition
  needs side conditions on deadlocks and liveness that are not decidable; the twin is a sufficient
  condition that gives them, so that the certificate preserves liveness and deadlocks like the
  others. Boundedness alone is preserved without any condition (see
  `PetriNet.IsSelfLoopTransition.bounded_removeTransition_iff`): `reduceBounded` is a search for
  boundedness only, which also deletes every self-loop transition
  (`tryRemoveAnySelfLoopTransition`). Its certificate is the equivalence of boundedness
  (`boundedSystem`), not `ReducesTo`.
- `tryRemoveParallelPlace`, `tryRemoveSelfLoopPlace`, `tryRemoveIsolatedPlace`: delete a place.

`ExecPetriNet.step` tries the rules in this order. For workflow nets, `tryFuseDrainWF` fuses a
drained place that is neither the source nor the sink, and `tryRemoveParallelTransitionWF` deletes a
parallel transition, as in `ReducesWF`; the other rules do not transfer soundness.

## Main statements

- `ExecPetriNet.reduce`: the iteration, with `ExecPetriNet.Reduced` bundling the result.
- `ExecPetriNet.reduce_normal`: the result is a fixed point: `step` finds no rule applicable
  (`step_eq_none_iff` unfolds this into the side conditions of the rules).
- `ExecPetriNet.reduceWF`, `ExecPetriNet.reduceWF_normal`: the same for workflow nets.
- `ExecPetriNet.reduceBounded`, `ExecPetriNet.reduceBounded_normal`: the same for boundedness only,
  with one more rule.

Fusion of a drained place reduces the reachable markings; the other rules do not (they only delete a
place or a transition), but they can enable fusions. The order of the rules does not guarantee that
the result is the smallest possible net.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

/-! ### Reduction systems

The iteration of a search does not depend on the data that is carried along a reduction: the
initial marking, or the source and the sink of a workflow net. It is written once for a
`ReductionSystem`. -/

/-- A notion of reduction between executable nets over `Fin`, together with the `Data` that is
carried along: a marking, or a source and a sink. -/
structure ReductionSystem where
  /-- The data on a net with `n` places. -/
  Data : ℕ → Type
  /-- The second net with its data is a reduction of the first. -/
  Reduces : ∀ {n m n' m' : ℕ}, ExecPetriNet (Fin n) (Fin m) → Data n →
    ExecPetriNet (Fin n') (Fin m') → Data n' → Prop
  /-- The empty reduction. -/
  refl : ∀ {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : Data n), Reduces N d N d
  /-- Reductions compose. -/
  trans : ∀ {n₀ m₀ n₁ m₁ n₂ m₂ : ℕ} {N₀ : ExecPetriNet (Fin n₀) (Fin m₀)} {d₀ : Data n₀}
    {N₁ : ExecPetriNet (Fin n₁) (Fin m₁)} {d₁ : Data n₁} {N₂ : ExecPetriNet (Fin n₂) (Fin m₂)}
    {d₂ : Data n₂}, Reduces N₀ d₀ N₁ d₁ → Reduces N₁ d₁ N₂ d₂ → Reduces N₀ d₀ N₂ d₂

/-- Reductions of nets with an initial marking: `ExecPetriNet.ReducesTo`. -/
abbrev markedSystem : ReductionSystem where
  Data n := Multiset (Fin n)
  Reduces N M₀ N' M₀' := N.ReducesTo M₀ N' M₀'
  refl N M₀ := ReducesTo.refl N M₀
  trans h₁ h₂ := h₁.trans h₂

/-- Reductions of workflow nets with a source and a sink: `ExecPetriNet.ReducesWF`. -/
abbrev workflowSystem : ReductionSystem where
  Data n := Fin n × Fin n
  Reduces N d N' d' := N.ReducesWF d.1 d.2 N' d'.1 d'.2
  refl N d := ReducesWF.refl N d.1 d.2
  trans h₁ h₂ := h₁.trans h₂

variable (S : ReductionSystem)

/-- A reduction of the net `N` with data `d` by any number of steps: a net over `Fin places` and
`Fin transitions`, with its data. -/
structure Reduct {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n) where
  /-- The number of places of the reduced net. -/
  places : ℕ
  /-- The number of transitions of the reduced net. -/
  transitions : ℕ
  /-- The reduced net. -/
  net : ExecPetriNet (Fin places) (Fin transitions)
  /-- The data of the reduced net. -/
  data : S.Data places
  /-- The reduced net is a reduction of the original net. -/
  reduces : S.Reduces N d net data
  /-- Places and transitions have not become more. -/
  le : places + transitions ≤ n + m

/-- One step of the reduction of `N` with data `d`: a reduction that is smaller. -/
structure ReductionStep {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n) where
  /-- The number of places of the reduced net. -/
  places : ℕ
  /-- The number of transitions of the reduced net. -/
  transitions : ℕ
  /-- The reduced net. -/
  net : ExecPetriNet (Fin places) (Fin transitions)
  /-- The data of the reduced net. -/
  data : S.Data places
  /-- The reduced net is a reduction of the original net. -/
  reduces : S.Reduces N d net data
  /-- Places and transitions have become fewer. -/
  lt : places + transitions < n + m

variable {S} {n m : ℕ} {N : ExecPetriNet (Fin n) (Fin m)} {d : S.Data n}

/-- The empty reduction. -/
def Reduct.refl (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n) : Reduct S N d :=
  ⟨n, m, N, d, S.refl N d, le_rfl⟩

/-- Follow a step by a further reduction. -/
def ReductionStep.extend (s : ReductionStep S N d) (r : Reduct S s.net s.data) : Reduct S N d :=
  ⟨r.places, r.transitions, r.net, r.data, S.trans s.reduces r.reduces, r.le.trans s.lt.le⟩

/-- Reductions that preserve and reflect boundedness only. More rules preserve boundedness than
preserve every property of `ExecPetriNet.ReducesTo`: any self-loop transition can be deleted. -/
abbrev boundedSystem : ReductionSystem where
  Data n := Multiset (Fin n)
  Reduces N M₀ N' M₀' :=
    N'.toPetriNet.Bounded (Multiset.toFinsupp M₀') ↔ N.toPetriNet.Bounded (Multiset.toFinsupp M₀)
  refl _ _ := Iff.rfl
  trans h₁ h₂ := h₂.trans h₁

namespace ReductionSystem

/-- A net with no places and no transitions has no step. -/
theorem step_eq_none_of_size_eq_zero
    (step : ∀ {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n),
      Option (ReductionStep S N d))
    (h : n + m = 0) : step N d = none := by
  cases hs : step N d with
  | none => rfl
  | some s => have := s.lt; omega

/-- Apply a step function until it finds no step, or the fuel runs out. -/
def reduceAll
    (step : ∀ {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n),
      Option (ReductionStep S N d)) :
    (fuel : ℕ) → {n m : ℕ} → (N : ExecPetriNet (Fin n) (Fin m)) → (d : S.Data n) →
      Reduct S N d
  | 0, _, _, N, d => .refl N d
  | fuel + 1, _, _, N, d =>
    match step N d with
    | none => .refl N d
    | some s => s.extend (reduceAll step fuel s.net s.data)

/-- With one unit of fuel for each place and transition, the result of `reduceAll` is a fixed
point: the step function finds no step. -/
theorem reduceAll_normal
    (step : ∀ {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n),
      Option (ReductionStep S N d)) :
    ∀ (fuel : ℕ) {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (d : S.Data n), n + m ≤ fuel →
      step (reduceAll step fuel N d).net (reduceAll step fuel N d).data = none
  | 0, _, _, N, d, h => by
    simpa [reduceAll, Reduct.refl] using step_eq_none_of_size_eq_zero step (N := N) (d := d)
      (by omega)
  | fuel + 1, _, _, N, d, h => by
    simp only [reduceAll]
    split
    · next hs => simpa [Reduct.refl] using hs
    · next s hs =>
      have := s.lt
      exact reduceAll_normal step fuel s.net s.data (by omega)

end ReductionSystem


/-! ### Side conditions of the rules -/

section Conditions

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m))

/-- The side conditions of fusing a drained place with the transition that drains it: `t` drains
`p`, it produces a token somewhere, and some transition produces into `p`. -/
abbrev CanFuseDrain (t : Fin m) (p : Fin n) : Prop :=
  N.toPetriNet.IsDrain t p ∧ N.post t ≠ 0 ∧ ∃ t₁, p ∈ N.post t₁

/-- The side conditions of fusing a drained place in a workflow net: the place is neither the
source nor the sink. -/
abbrev CanFuseDrainWF (i o : Fin n) (t : Fin m) (p : Fin n) : Prop :=
  N.toPetriNet.IsDrain t p ∧ i ≠ p ∧ o ≠ p

/-- The side conditions of deleting the place `p` as a parallel place: a parallel place `q` has no
more tokens initially. -/
abbrev CanRemoveParallelPlace (M₀ : Multiset (Fin n)) (p q : Fin n) : Prop :=
  N.toPetriNet.ParallelPlaces p q ∧ M₀.count q ≤ M₀.count p

/-- The side conditions of deleting the place `p` as a self-loop place. -/
abbrev CanRemoveSelfLoopPlace (M₀ : Multiset (Fin n)) (p : Fin n) : Prop :=
  (∀ t, (N.pre t).count p ≤ M₀.count p) ∧ ∀ t, (N.post t).count p = (N.pre t).count p

/-- The side conditions of deleting the transition `t` as a self-loop transition with a twin: `t`
has equal preset and postset, and some other transition has the same preset. -/
abbrev CanRemoveSelfLoopTransition (t : Fin m) : Prop :=
  N.pre t = N.post t ∧ ∃ u, u ≠ t ∧ N.pre u = N.pre t

end Conditions

/-! ### Steps -/

section Steps

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n))

/-- The step that deletes the place `p`. -/
def ReductionStep.ofRemovePlace (p : Fin n)
    (h : N.ReducesTo M₀ (N.removePlace p) (dropMarking p M₀)) :
    ReductionStep markedSystem N M₀ where
  places := n - 1
  transitions := m
  net := (N.removePlaceFin p).tabulate
  data := dropFin p M₀
  reduces := by
    rw [tabulate_eq]
    exact h.trans (ReducesTo.reindexPlaces (skipEquiv p))
  lt := by have := p.pos; omega

/-- The step that deletes the transition `t`. -/
def ReductionStep.ofRemoveTransition (t : Fin m)
    (h : N.ReducesTo M₀ (N.removeTransition t) M₀) : ReductionStep markedSystem N M₀ where
  places := n
  transitions := m - 1
  net := (N.removeTransitionFin t).tabulate
  data := M₀
  reduces := by
    rw [tabulate_eq]
    exact h.trans (ReducesTo.reindexTransitions (skipEquiv t))
  lt := by have := t.pos; omega

/-- The step that fuses the transition `t` into the place `p`, and deletes both. -/
def ReductionStep.ofFuse (t : Fin m) (p : Fin n)
    (h : N.ReducesTo M₀ (N.fuseDelete t p) (dropMarking p (N.collapseMarking t p M₀))) :
    ReductionStep markedSystem N M₀ where
  places := n - 1
  transitions := m - 1
  net := (N.fuseFin t p).tabulate
  data := N.collapseFin t p M₀
  reduces := by
    rw [tabulate_eq]
    exact h.trans (ReducesTo.reindex (skipEquiv p) (skipEquiv t))
  lt := by have := t.pos; have := p.pos; omega

end Steps

section Search

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n))

/-- Fuse the first drained place with its draining transition, if there is one. -/
def tryFuseDrain : Option (ReductionStep markedSystem N M₀) :=
  tryPair (N.CanFuseDrain) fun t p h =>
    .ofFuse N M₀ t p (ReducesTo.fuseDrain h.1 h.2.1 h.2.2)

/-- Delete the second of the first two parallel transitions, if there are any. -/
def tryRemoveParallelTransition : Option (ReductionStep markedSystem N M₀) :=
  tryPair (fun t₁ t₂ : Fin m => N.toPetriNet.ParallelTransitions t₁ t₂) fun _ t₂ h =>
    .ofRemoveTransition N M₀ t₂ (ReducesTo.removeParallelTransition h)

/-- Delete the first self-loop transition that has a twin with the same preset, if there is
one. -/
def tryRemoveSelfLoopTransition : Option (ReductionStep markedSystem N M₀) :=
  tryFin (N.CanRemoveSelfLoopTransition) fun t h =>
    .ofRemoveTransition N M₀ t (by
      obtain ⟨hloop, u, hu, hpre⟩ := h
      exact ReducesTo.selfLoopTransition_of_twin hloop hu hpre)

/-- Delete the first place that is parallel to a place with no more tokens, if there is one. -/
def tryRemoveParallelPlace : Option (ReductionStep markedSystem N M₀) :=
  tryPair (N.CanRemoveParallelPlace M₀) fun p _ h =>
    .ofRemovePlace N M₀ p (ReducesTo.parallelPlace h.1 h.2)

/-- Delete the first self-loop place, if there is one. -/
def tryRemoveSelfLoopPlace : Option (ReductionStep markedSystem N M₀) :=
  tryFin (N.CanRemoveSelfLoopPlace M₀) fun p h =>
    .ofRemovePlace N M₀ p (ReducesTo.selfLoopPlace p h.1 h.2)

/-- Delete the first isolated place, if there is one. -/
def tryRemoveIsolatedPlace : Option (ReductionStep markedSystem N M₀) :=
  tryFin (fun p : Fin n => N.toPetriNet.IsIsolated p) fun p h =>
    .ofRemovePlace N M₀ p (ReducesTo.isolatedPlace h)

/-- One step of the reduction: the first rule that applies, in the order fusion of a drained place,
parallel transitions, self-loop transitions, parallel places, self-loop places, isolated places. -/
def step : Option (ReductionStep markedSystem N M₀) :=
  N.tryFuseDrain M₀ <|> N.tryRemoveParallelTransition M₀ <|> N.tryRemoveSelfLoopTransition M₀ <|>
    N.tryRemoveParallelPlace M₀ <|> N.tryRemoveSelfLoopPlace M₀ <|> N.tryRemoveIsolatedPlace M₀

/-- No rule applies exactly when none of the six rules has an instance. -/
theorem step_eq_none_iff :
    N.step M₀ = none ↔
      (∀ t p, ¬ N.CanFuseDrain t p) ∧ (∀ t₁ t₂, ¬ N.toPetriNet.ParallelTransitions t₁ t₂) ∧
        (∀ t, ¬ N.CanRemoveSelfLoopTransition t) ∧ (∀ p q, ¬ N.CanRemoveParallelPlace M₀ p q) ∧
        (∀ p, ¬ N.CanRemoveSelfLoopPlace M₀ p) ∧ ∀ p, ¬ N.toPetriNet.IsIsolated p := by
  simp only [step, Option.orElse_eq_none, tryFuseDrain, tryRemoveParallelTransition,
    tryRemoveSelfLoopTransition, tryRemoveParallelPlace, tryRemoveSelfLoopPlace,
    tryRemoveIsolatedPlace, tryPair_eq_none_iff, tryFin_eq_none_iff]

end Search

/-- The result of reducing a net with an initial marking. -/
abbrev Reduced {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n)) :=
  Reduct markedSystem N M₀

/-- The initial marking of the reduced net. -/
def Reduced.init {n m : ℕ} {N : ExecPetriNet (Fin n) (Fin m)} {M₀ : Multiset (Fin n)}
    (r : Reduced N M₀) : Multiset (Fin r.places) :=
  r.data

/-- Reduce a net by the first rule that applies, until no rule applies. Every step deletes a place
or a transition, so one unit of fuel for each is enough. -/
def reduce {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n)) : Reduced N M₀ :=
  markedSystem.reduceAll (fun N M₀ => N.step M₀) (n + m) N M₀

/-- The result of `reduce` is a fixed point: no rule applies to it. -/
theorem reduce_normal {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n)) :
    (reduce N M₀).net.step (reduce N M₀).init = none :=
  markedSystem.reduceAll_normal (fun N M₀ => N.step M₀) (n + m) N M₀ le_rfl

/-! ### Boundedness only -/

section SearchBounded

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n))

/-- A step of the search for a certificate is a step for boundedness. -/
def ReductionStep.toBounded (s : ReductionStep markedSystem N M₀) :
    ReductionStep boundedSystem N M₀ :=
  ⟨s.places, s.transitions, s.net, s.data, s.reduces.bounded_iff, s.lt⟩

/-- The step that deletes the self-loop transition `t`. -/
def ReductionStep.ofSelfLoopTransition (t : Fin m) (h : N.pre t = N.post t) :
    ReductionStep boundedSystem N M₀ where
  places := n
  transitions := m - 1
  net := (N.removeTransitionFin t).tabulate
  data := M₀
  reduces := by
    rw [tabulate_eq]
    exact (ReducesTo.reindexTransitions (N := N.removeTransition t) (M₀ := M₀)
      (skipEquiv t)).bounded_iff.trans (ReducesTo.bounded_removeTransition_of_pre_eq_post h)
  lt := by have := t.pos; omega

/-- Delete the first self-loop transition, if there is one. Boundedness is preserved without a
twin, unlike deadlocks and liveness. -/
def tryRemoveAnySelfLoopTransition : Option (ReductionStep boundedSystem N M₀) :=
  tryFin (fun t : Fin m => N.pre t = N.post t) fun t h =>
    .ofSelfLoopTransition N M₀ t h

/-- One step of the reduction for boundedness: the rules of `step`, then deleting any self-loop
transition. -/
def stepBounded : Option (ReductionStep boundedSystem N M₀) :=
  (N.step M₀).map (ReductionStep.toBounded N M₀) <|> N.tryRemoveAnySelfLoopTransition M₀

/-- No rule applies exactly when no rule of `step` applies and no transition is a self-loop. -/
theorem stepBounded_eq_none_iff :
    N.stepBounded M₀ = none ↔ N.step M₀ = none ∧ ∀ t, ¬ N.pre t = N.post t := by
  simp only [stepBounded, Option.orElse_eq_none, Option.map_eq_none_iff,
    tryRemoveAnySelfLoopTransition, tryFin_eq_none_iff]

end SearchBounded

/-- Reduce a net by the rules that preserve boundedness, until no rule applies. -/
def reduceBounded {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n)) :
    Reduct boundedSystem N M₀ :=
  boundedSystem.reduceAll (fun N M₀ => N.stepBounded M₀) (n + m) N M₀

/-- The result of `reduceBounded` is a fixed point: no rule applies to it. -/
theorem reduceBounded_normal {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m))
    (M₀ : Multiset (Fin n)) :
    (reduceBounded N M₀).net.stepBounded (reduceBounded N M₀).data = none :=
  boundedSystem.reduceAll_normal (fun N M₀ => N.stepBounded M₀) (n + m) N M₀ le_rfl

/-! ### Workflow nets -/

section SearchWF

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (i o : Fin n)

/-- The step that fuses the transition `t` into the place `p` in a workflow net whose source and
sink are not `p`, and deletes both. -/
def ReductionStep.ofFuseWF (t : Fin m) (p : Fin n) (hi : i ≠ p) (ho : o ≠ p)
    (h : N.ReducesWF i o (N.fuseDelete t p) ⟨i, hi⟩ ⟨o, ho⟩) :
    ReductionStep workflowSystem N (i, o) where
  places := n - 1
  transitions := m - 1
  net := (N.fuseFin t p).tabulate
  data := (skipEquiv p ⟨i, hi⟩, skipEquiv p ⟨o, ho⟩)
  reduces := by
    rw [tabulate_eq]
    exact h.trans (ReducesWF.reindex (skipEquiv p) (skipEquiv t))
  lt := by have := t.pos; have := p.pos; omega

/-- The step that deletes the transition `t` from a workflow net. -/
def ReductionStep.ofRemoveTransitionWF (t : Fin m)
    (h : N.ReducesWF i o (N.removeTransition t) i o) :
    ReductionStep workflowSystem N (i, o) where
  places := n
  transitions := m - 1
  net := (N.removeTransitionFin t).tabulate
  data := (i, o)
  reduces := by
    rw [tabulate_eq]
    exact h.trans (ReducesWF.reindexTransitions (skipEquiv t))
  lt := by have := t.pos; omega

/-- Delete the second of the first two parallel transitions in a workflow net, if there are
any. -/
def tryRemoveParallelTransitionWF : Option (ReductionStep workflowSystem N (i, o)) :=
  tryPair (fun t₁ t₂ : Fin m => N.toPetriNet.ParallelTransitions t₁ t₂) fun _ t₂ h =>
    .ofRemoveTransitionWF N i o t₂ (ReducesWF.removeParallelTransition h)

/-- Fuse the first drained place with its draining transition in a workflow net, if there is one
that is neither the source nor the sink. -/
def tryFuseDrainWF : Option (ReductionStep workflowSystem N (i, o)) :=
  tryPair (N.CanFuseDrainWF i o) fun t p h =>
    .ofFuseWF N i o t p h.2.1 h.2.2 (ReducesWF.fuseDrain h.1 h.2.1 h.2.2)

/-- One step of the reduction of a workflow net: fusion of a drained place, then deletion of a
parallel transition. -/
def stepWF : Option (ReductionStep workflowSystem N (i, o)) :=
  N.tryFuseDrainWF i o <|> N.tryRemoveParallelTransitionWF i o

/-- No rule applies exactly when no drained place is neither the source nor the sink, and no
transitions are parallel. -/
theorem stepWF_eq_none_iff :
    N.stepWF i o = none ↔ (∀ t p, ¬ N.CanFuseDrainWF i o t p) ∧
      ∀ t₁ t₂, ¬ N.toPetriNet.ParallelTransitions t₁ t₂ := by
  simp only [stepWF, Option.orElse_eq_none, tryFuseDrainWF, tryRemoveParallelTransitionWF,
    tryPair_eq_none_iff]

end SearchWF

/-- The result of reducing a workflow net with a source and a sink. -/
abbrev ReducedWF {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (i o : Fin n) :=
  Reduct workflowSystem N (i, o)

/-- The source of the reduced workflow net. -/
def ReducedWF.source {n m : ℕ} {N : ExecPetriNet (Fin n) (Fin m)} {i o : Fin n}
    (r : ReducedWF N i o) : Fin r.places :=
  r.data.1

/-- The sink of the reduced workflow net. -/
def ReducedWF.sink {n m : ℕ} {N : ExecPetriNet (Fin n) (Fin m)} {i o : Fin n}
    (r : ReducedWF N i o) : Fin r.places :=
  r.data.2

/-- Reduce a workflow net by fusing drained places and deleting parallel transitions, until none
applies. Every step deletes a place or a transition, so one unit of fuel for each is enough. -/
def reduceWF {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (i o : Fin n) : ReducedWF N i o :=
  workflowSystem.reduceAll (fun N d => N.stepWF d.1 d.2) (n + m) N (i, o)

/-- The result of `reduceWF` is a fixed point: no drained place can be fused. -/
theorem reduceWF_normal {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (i o : Fin n) :
    (reduceWF N i o).net.stepWF (reduceWF N i o).source (reduceWF N i o).sink = none :=
  workflowSystem.reduceAll_normal (fun N d => N.stepWF d.1 d.2) (n + m) N (i, o) le_rfl

end ExecPetriNet

end Cslib
