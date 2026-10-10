/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics

/-! # Labelled Petri nets

The marking graph `PetriNet.lts` uses the transitions themselves as labels. A *labelled* net
additionally gives each transition an observable label, with several transitions allowed to share
one. This is how Petri nets are compared with process calculi, where the same action can be
performed in different ways.

## Main definitions

- `PetriNet.labelledLts`: the marking graph of a net whose transitions are relabelled by a function.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} {Label : Type*}

/-- The marking graph of a net, with each transition replaced by its label `ℓ t`. -/
def labelledLts (N : PetriNet Place Transition) (ℓ : Transition → Label) :
    LTS (Marking Place) Label where
  Tr M a M' := ∃ t, ℓ t = a ∧ M [t⟩[N] M'

theorem labelledLts_tr_iff {N : PetriNet Place Transition} {ℓ : Transition → Label}
    {M M' : Marking Place} {a : Label} :
    (N.labelledLts ℓ).Tr M a M' ↔ ∃ t, ℓ t = a ∧ M [t⟩[N] M' := Iff.rfl

/-- Firing a transition is a step of the labelled marking graph, labelled by the transition. -/
theorem Fires.labelledLts {N : PetriNet Place Transition} {ℓ : Transition → Label}
    {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    (N.labelledLts ℓ).Tr M (ℓ t) M' :=
  ⟨t, rfl, h⟩

end PetriNet

end Cslib
