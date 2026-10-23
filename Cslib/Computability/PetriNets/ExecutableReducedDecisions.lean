/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.CTL
public import Cslib.Computability.PetriNets.ExecutableReduction
public import Cslib.Computability.PetriNets.ExecutableSoundness

/-! # Deciding properties of a net through a reduction

Given a certificate `h : N.ReducesTo M₀ N' M₀'` (or `h : N.ReducesWF i o N' i' o'` for workflow
nets) that `N'` is a reduction of `N`, a property of `N` is decided by deciding it for `N'`, using
the decision procedures for executable nets, and transferring the answer along the iff-lemmas of
`ExecPetriNet.ReducesTo`. The certificate is supplied by the user; the search for reductions is in
`Cslib.Computability.PetriNets.ExecutableAutoDecisions`. The certificate is a proof, which `decide`
never evaluates, so only the reduced net is evaluated.

## Main definitions

- `ExecPetriNet.decidableAndOfImp`: a conjunction whose second conjunct is decided under the first.
- `ExecPetriNet.decidableBoundedOfReducesTo`: boundedness through a certificate.
- `ExecPetriNet.decidableLiveOfReducesTo`: liveness, if the reduced net is bounded.
- `ExecPetriNet.decidableDeadlockOfReducesTo`, `ExecPetriNet.decidableDeadlockFreeOfReducesTo`:
  the reachability of a dead marking, if the reduced net is bounded.
- `ExecPetriNet.decidableSoundOfReducesWF`: soundness of a workflow net.

Reductions of places make the net smaller, but not its set of reachable markings. Reductions of
series transitions and places also make the number of reachable markings smaller, which is the
point: see the examples in `CslibTests.ReducedDecisions`.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

universe u v

/-- A conjunction is decidable if the second conjunct is decidable under the first. -/
def decidableAndOfImp {P Q : Prop} (hP : Decidable P) (hQ : P → Decidable Q) : Decidable (P ∧ Q) :=
  match hP with
  | .isTrue hp =>
    match hQ hp with
    | .isTrue hq => .isTrue ⟨hp, hq⟩
    | .isFalse hq => .isFalse fun h => hq h.2
  | .isFalse hp => .isFalse fun h => hp h.1

section Decisions

variable {Place Place' : Type u} {Transition Transition' : Type v} [DecidableEq Place]
  [DecidableEq Place'] [Fintype Place'] [Fintype Transition']
  {N : ExecPetriNet Place Transition} {M₀ : Multiset Place}
  {N' : ExecPetriNet Place' Transition'} {M₀' : Multiset Place'}

/-- Boundedness of `N` is decided on the reduced net `N'`. -/
def decidableBoundedOfReducesTo (h : N.ReducesTo M₀ N' M₀') :
    Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :=
  decidable_of_iff _ h.bounded_iff

/-- Liveness of `N` is decided on the reduced net `N'`, which has to be bounded. -/
def decidableLiveOfReducesTo (h : N.ReducesTo M₀ N' M₀')
    (hb : N'.toPetriNet.Bounded (Multiset.toFinsupp M₀')) :
    Decidable (N.toPetriNet.Live (Multiset.toFinsupp M₀)) :=
  @decidable_of_iff _ _ h.live_iff (decidableLive M₀' hb)

/-- The reachability of a dead marking in `N` is decided on the reduced net `N'`, which has to be
bounded. -/
def decidableDeadlockOfReducesTo (h : N.ReducesTo M₀ N' M₀')
    (hb : N'.toPetriNet.Bounded (Multiset.toFinsupp M₀')) :
    Decidable (∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M) :=
  @decidable_of_iff _ _ h.exists_dead_iff (decidableDeadlock M₀' hb)

/-- Deadlock-freedom of `N` is decided on the reduced net `N'`, which has to be bounded. -/
def decidableDeadlockFreeOfReducesTo (h : N.ReducesTo M₀ N' M₀')
    (hb : N'.toPetriNet.Bounded (Multiset.toFinsupp M₀')) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  have := decidableDeadlockOfReducesTo h hb
  decidable_of_iff (¬ ∃ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M ∧ N.toPetriNet.Dead M)
    (by simp only [not_exists, not_and])

/-- Soundness of the workflow net `N` is decided on the reduced workflow net `N'`. -/
def decidableSoundOfReducesWF {i o : Place} {i' o' : Place'} (h : N.ReducesWF i o N' i' o')
    (hN : N.toPetriNet.IsWFNet i o) : Decidable (N.toPetriNet.Sound i o) :=
  decidable_of_iff _ (h.isWFNet_and_sound hN).2

end Decisions

end ExecPetriNet

end Cslib
