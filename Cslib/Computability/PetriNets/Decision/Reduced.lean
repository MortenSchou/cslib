/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.CTL
public import Cslib.Computability.PetriNets.Decision.Soundness
public import Cslib.Computability.PetriNets.ReducesTo

/-! # Deciding properties of a net through a reduction

Given a certificate `h : ReducesTo N M₀ N' M₀'` (or `h : ReducesWF N i o N' i' o'` for workflow
nets) that `N'` is a reduction of `N`, a property of `N` is decided by deciding it for `N'` and
transferring the answer along the iff-lemmas of `PetriNet.ReducesTo` and `PetriNet.ReducesWF`. The
certificate is supplied by the user; the search for reductions is in
`Cslib.Computability.PetriNets.Decision.AutoReduction`. It is a proof, which `decide` never
evaluates, so only the reduced net is evaluated; the original net need not even have finitely many
places or transitions.

## Main definitions

- `PetriNet.decidableAndOfImp`: a conjunction whose second conjunct is decided under the first.
- `PetriNet.decidableBoundedOfReducesTo`: boundedness through a certificate.
- `PetriNet.decidableLiveOfReducesTo`: liveness, if the reduced net is bounded.
- `PetriNet.decidableDeadlockOfReducesTo`, `PetriNet.decidableDeadlockFreeOfReducesTo`: the
  reachability of a dead marking, if the reduced net is bounded.
- `PetriNet.decidableSoundOfReducesWF`: soundness of a workflow net.

Reductions of places make the net smaller, but not its set of reachable markings. Reductions of
series transitions and places also make the number of reachable markings smaller, which is the
point: see the examples in `CslibTests.ReducedDecisions`.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

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

variable {Place Place' : Type u} {Transition Transition' : Type v} [DecidableEq Place']
  [Fintype Place'] [Fintype Transition'] {N : PetriNet Place Transition} {M₀ : Marking Place}
  {N' : PetriNet Place' Transition'} {M₀' : Marking Place'}

/-- Boundedness of `N` is decided on the reduced net `N'`. -/
def decidableBoundedOfReducesTo (h : ReducesTo N M₀ N' M₀') : Decidable (N.Bounded M₀) :=
  decidable_of_iff _ h.bounded_iff

/-- Liveness of `N` is decided on the reduced net `N'`, which has to be bounded. -/
def decidableLiveOfReducesTo (h : ReducesTo N M₀ N' M₀') (hb : N'.Bounded M₀') :
    Decidable (N.Live M₀) :=
  @decidable_of_iff _ _ h.live_iff (decidableLive M₀' hb)

/-- The reachability of a dead marking in `N` is decided on the reduced net `N'`, which has to be
bounded. -/
def decidableDeadlockOfReducesTo (h : ReducesTo N M₀ N' M₀') (hb : N'.Bounded M₀') :
    Decidable (∃ M, M₀ ⇝[N] M ∧ N.Dead M) :=
  @decidable_of_iff _ _ h.exists_dead_iff (decidableDeadlock M₀' hb)

/-- Deadlock-freedom of `N` is decided on the reduced net `N'`, which has to be bounded. -/
def decidableDeadlockFreeOfReducesTo (h : ReducesTo N M₀ N' M₀') (hb : N'.Bounded M₀') :
    Decidable (∀ M, M₀ ⇝[N] M → ¬ N.Dead M) :=
  have := decidableDeadlockOfReducesTo h hb
  decidable_of_iff (¬ ∃ M, M₀ ⇝[N] M ∧ N.Dead M) (by simp only [not_exists, not_and])

/-- Soundness of the workflow net `N` is decided on the reduced workflow net `N'`. -/
def decidableSoundOfReducesWF {i o : Place} {i' o' : Place'} (h : ReducesWF N i o N' i' o')
    (hN : N.IsWFNet i o) : Decidable (N.Sound i o) :=
  decidable_of_iff _ (h.isWFNet_and_sound hN).2

end PetriNet

end Cslib
