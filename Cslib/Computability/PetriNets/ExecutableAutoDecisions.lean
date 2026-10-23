/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableReducedDecisions
public import Cslib.Computability.PetriNets.ExecutableReductionSearch

/-! # Deciding properties of a net by reducing it automatically

The decision procedures of `Cslib.Computability.PetriNets.ExecutableReducedDecisions` take a
certificate of reduction from the user. Here the certificate comes from the search
`ExecPetriNet.reduce` (`ExecPetriNet.reduceWF` for workflow nets) of
`Cslib.Computability.PetriNets.ExecutableReductionSearch`: the net is reduced by the rules that
apply, and the property is decided on the reduced net by the existing decision procedure.

The nets are executable nets over `Fin n` places and `Fin m` transitions. The reduced net is
evaluated by the kernel (`decide +kernel`), so a decision is run as in

`of_decide_eq_true (inst := decideBoundedReduced N M₀) (by decide +kernel)`.

## Main definitions

- `ExecPetriNet.decideBoundedReduced`: boundedness.
- `ExecPetriNet.decideLiveReduced`, `ExecPetriNet.decideDeadlockFreeReduced`: liveness and
  deadlock-freedom of a bounded net; `ExecPetriNet.decideBoundedAndLiveReduced` and
  `ExecPetriNet.decideBoundedAndDeadlockFreeReduced` do not assume boundedness.
- `ExecPetriNet.decideSoundReduced`: soundness of a workflow net;
  `ExecPetriNet.decideWFNetAndSoundReduced` also decides that the net is a workflow net.

Boundedness is decided on the net reduced by `ExecPetriNet.reduceBounded`, which has the rules of
`ExecPetriNet.reduce` and also deletes any self-loop transition: boundedness is preserved without
the side conditions that liveness and deadlocks need.

The `…Equiv` variants take bijections with `Fin n` and `Fin m` for a net over arbitrary types of
places and transitions, and go through `ExecPetriNet.ReducesTo.reindex`.

Liveness and deadlock-freedom are decided on the reduced net only when it is bounded, which by
`ExecPetriNet.ReducesTo.bounded_iff` is the case iff the original net is. Soundness is transferred
along `ReducesWF`, hence only through series fusions, and the original net has to be a workflow
net; the reduced net is then one as well.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet
open scoped PetriNet

variable {n m : ℕ} (N : ExecPetriNet (Fin n) (Fin m)) (M₀ : Multiset (Fin n))

/-- Boundedness of `N` at `M₀`, decided on the automatically reduced net. The reduction is
`reduceBounded`, which also deletes self-loop transitions that have no twin. -/
def decideBoundedReduced : Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :=
  decidable_of_iff _ (reduceBounded N M₀).reduces

/-- Liveness of the bounded net `N` at `M₀`, decided on the automatically reduced net. -/
def decideLiveReduced (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (N.toPetriNet.Live (Multiset.toFinsupp M₀)) :=
  decidableLiveOfReducesTo (reduce N M₀).reduces ((reduce N M₀).reduces.bounded_iff.2 hb)

/-- Deadlock-freedom of the bounded net `N` at `M₀`, decided on the automatically reduced net. -/
def decideDeadlockFreeReduced (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableDeadlockFreeOfReducesTo (reduce N M₀).reduces ((reduce N M₀).reduces.bounded_iff.2 hb)

/-- Boundedness and liveness of `N` at `M₀`, decided on the automatically reduced net. -/
def decideBoundedAndLiveReduced :
    Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀) ∧
      N.toPetriNet.Live (Multiset.toFinsupp M₀)) :=
  decidableAndOfImp (decideBoundedReduced N M₀) (decideLiveReduced N M₀)

/-- Boundedness and deadlock-freedom of `N` at `M₀`, decided on the automatically reduced net. -/
def decideBoundedAndDeadlockFreeReduced :
    Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀) ∧
      ∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableAndOfImp (decideBoundedReduced N M₀) (decideDeadlockFreeReduced N M₀)

variable (i o : Fin n)

/-- Soundness of the workflow net `N`, decided on the automatically reduced net. -/
def decideSoundReduced (hN : N.toPetriNet.IsWFNet i o) : Decidable (N.toPetriNet.Sound i o) :=
  decidableSoundOfReducesWF (reduceWF N i o).reduces hN

/-- Whether `N` is a workflow net and sound, decided with the automatically reduced net. -/
def decideWFNetAndSoundReduced [h : Decidable (N.toPetriNet.IsWFNet i o)] :
    Decidable (N.toPetriNet.IsWFNet i o ∧ N.toPetriNet.Sound i o) :=
  decidableAndOfImp h (decideSoundReduced N i o)

/-! ### Nets over arbitrary finite types

A net over any types of places and transitions is decided through bijections with `Fin n` and
`Fin m`: the net is renamed (`ExecPetriNet.rename`), which preserves every property
(`ExecPetriNet.ReducesTo.reindex`), and the renamed net is reduced and decided as above. The
bijections are explicit arguments, so the renamed net is evaluated by the kernel. -/

section Equiv

variable {Place Transition : Type} [DecidableEq Place] {n m : ℕ}
  (N : ExecPetriNet Place Transition) (e : Place ≃ Fin n) (f : Transition ≃ Fin m)
  (M₀ : Multiset Place)

/-- Boundedness of `N` at `M₀`, decided on the renamed and automatically reduced net. -/
def decideBoundedReducedEquiv : Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :=
  @decidable_of_iff _ _ (ReducesTo.reindex (N := N) (M₀ := M₀) e f).bounded_iff
    (decideBoundedReduced (N.rename e f) (M₀.map e))

/-- Liveness of the bounded net `N` at `M₀`, decided on the renamed and automatically reduced
net. -/
def decideLiveReducedEquiv (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (N.toPetriNet.Live (Multiset.toFinsupp M₀)) :=
  have h := ReducesTo.reindex (N := N) (M₀ := M₀) e f
  @decidable_of_iff _ _ h.live_iff
    (decideLiveReduced (N.rename e f) (M₀.map e) (h.bounded_iff.2 hb))

/-- Deadlock-freedom of the bounded net `N` at `M₀`, decided on the renamed and automatically
reduced net. -/
def decideDeadlockFreeReducedEquiv (hb : N.toPetriNet.Bounded (Multiset.toFinsupp M₀)) :
    Decidable (∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  have h := ReducesTo.reindex (N := N) (M₀ := M₀) e f
  @decidable_of_iff _ _ (deadlockFree_congr h.exists_dead_iff.symm).symm
    (decideDeadlockFreeReduced (N.rename e f) (M₀.map e) (h.bounded_iff.2 hb))

/-- Boundedness and liveness of `N` at `M₀`, decided on the renamed and automatically reduced
net. -/
def decideBoundedAndLiveReducedEquiv :
    Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀) ∧
      N.toPetriNet.Live (Multiset.toFinsupp M₀)) :=
  decidableAndOfImp (decideBoundedReducedEquiv N e f M₀) (decideLiveReducedEquiv N e f M₀)

/-- Boundedness and deadlock-freedom of `N` at `M₀`, decided on the renamed and automatically
reduced net. -/
def decideBoundedAndDeadlockFreeReducedEquiv :
    Decidable (N.toPetriNet.Bounded (Multiset.toFinsupp M₀) ∧
      ∀ M, (Multiset.toFinsupp M₀) ⇝[N.toPetriNet] M → ¬ N.toPetriNet.Dead M) :=
  decidableAndOfImp (decideBoundedReducedEquiv N e f M₀)
    (decideDeadlockFreeReducedEquiv N e f M₀)

variable (i o : Place)

/-- Soundness of the workflow net `N`, decided on the renamed and automatically reduced net. -/
def decideSoundReducedEquiv (hN : N.toPetriNet.IsWFNet i o) : Decidable (N.toPetriNet.Sound i o) :=
  have h := (ReducesWF.reindex (N := N) (i := i) (o := o) e f).isWFNet_and_sound hN
  @decidable_of_iff _ _ h.2 (decideSoundReduced (N.rename e f) (e i) (e o) h.1)

/-- Whether `N` is a workflow net and sound, decided with the renamed and automatically reduced
net. -/
def decideWFNetAndSoundReducedEquiv [h : Decidable (N.toPetriNet.IsWFNet i o)] :
    Decidable (N.toPetriNet.IsWFNet i o ∧ N.toPetriNet.Sound i o) :=
  decidableAndOfImp h (decideSoundReducedEquiv N e f i o)

end Equiv

end ExecPetriNet

end Cslib
