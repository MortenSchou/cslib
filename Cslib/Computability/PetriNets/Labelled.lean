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
- `PetriNet.hide`: the labelling that makes one transition invisible and keeps all others.
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

open scoped Classical in
/-- The labelling that hides the transition `t₂` (label `none`) and keeps every other transition
visible, labelled by itself. -/
noncomputable def hide (t₂ : Transition) : Transition → Option {t // t ≠ t₂} :=
  fun t => if h : t = t₂ then none else some ⟨t, h⟩

/-- The hidden transition has no label. -/
@[simp] theorem hide_self (t₂ : Transition) : hide t₂ t₂ = none := by
  simp [hide]

/-- Every other transition is labelled by itself. -/
theorem hide_of_ne {t t₂ : Transition} (h : t ≠ t₂) : hide t₂ t = some ⟨t, h⟩ := by
  simp [hide, h]

end PetriNet

end Cslib
