/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Automaton

/-! # Membership in the firing language of a net

A firing sequence belongs to the firing language of a net exactly when running it from the initial
marking succeeds in a final marking. This makes membership decidable, as soon as it is decidable
whether a marking is final.

## Main statements

- `PetriNet.mem_firingLanguage_iff`: membership is a successful `PetriNet.run` ending in a final
  marking.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type} [DecidableEq Place] {N : PetriNet Place Transition}

theorem mem_firingLanguage_iff {F : Set (Marking Place)} {M₀ : Marking Place}
    {ts : List Transition} :
    ts ∈ N.firingLanguage M₀ F ↔ ∃ M, N.run M₀ ts = some M ∧ M ∈ F := by
  simp only [firingLanguage, run_eq_some_iff]
  exact exists_congr fun _ => and_comm

/-- Membership in the firing language is decidable if finality of a marking is. -/
instance {F : Set (Marking Place)} [DecidablePred (· ∈ F)] (M₀ : Marking Place)
    (ts : List Transition) : Decidable (ts ∈ N.firingLanguage M₀ F) :=
  match h : N.run M₀ ts with
  | none => isFalse (by simp [mem_firingLanguage_iff, h])
  | some M => decidable_of_iff (M ∈ F) (by simp [mem_firingLanguage_iff, h])

end PetriNet

end Cslib
