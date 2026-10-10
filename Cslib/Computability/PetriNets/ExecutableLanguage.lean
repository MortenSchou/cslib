/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Automaton
public import Cslib.Computability.PetriNets.Executable

/-! # Membership in the firing language of an executable net

A firing sequence belongs to the firing language of an executable net exactly when running it from
the initial marking succeeds in a final marking. This makes membership decidable, as soon as it is
decidable whether the multiset of a marking is final.

## Main statements

- `ExecPetriNet.mem_firingLanguage_iff`: membership is a successful `ExecPetriNet.run` ending in a
  final marking.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

variable {Place Transition : Type} [DecidableEq Place] {N : ExecPetriNet Place Transition}

theorem mem_firingLanguage_iff {F : Set (PetriNet.Marking Place)} {M₀ : Multiset Place}
    {ts : List Transition} :
    ts ∈ N.toPetriNet.firingLanguage (Multiset.toFinsupp M₀) F ↔
      ∃ m, N.run M₀ ts = some m ∧ Multiset.toFinsupp m ∈ F := by
  constructor
  · rintro ⟨X, hX, h⟩
    obtain ⟨m, rfl⟩ := Multiset.toFinsupp.surjective X
    exact ⟨m, (run_eq_some_iff N).2 h, hX⟩
  · rintro ⟨m, hm, hF⟩
    exact ⟨Multiset.toFinsupp m, hF, (run_eq_some_iff N).1 hm⟩

/-- Membership in the firing language is decidable if finality of a multiset marking is. -/
instance {F : Set (PetriNet.Marking Place)} [DecidablePred fun m : Multiset Place =>
    Multiset.toFinsupp m ∈ F] (M₀ : Multiset Place) (ts : List Transition) :
    Decidable (ts ∈ N.toPetriNet.firingLanguage (Multiset.toFinsupp M₀) F) :=
  match h : N.run M₀ ts with
  | none => isFalse (by simp [mem_firingLanguage_iff, h])
  | some m => decidable_of_iff (Multiset.toFinsupp m ∈ F) (by simp [mem_firingLanguage_iff, h])

/-- A single final marking given by a multiset is decidable. -/
instance (m₀ : Multiset Place) : DecidablePred fun m : Multiset Place =>
    Multiset.toFinsupp m ∈ ({Multiset.toFinsupp m₀} : Set (PetriNet.Marking Place)) :=
  fun m => decidable_of_iff (m = m₀) (by simp [Multiset.toFinsupp.injective.eq_iff])

end ExecPetriNet

end Cslib
