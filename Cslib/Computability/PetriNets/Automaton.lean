/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.Automata.NA.Basic
public import Cslib.Computability.Languages.RegularLanguage
public import Cslib.Computability.PetriNets.Semantics

/-! # Petri nets as automata

The marking graph of a Petri net, with an initial marking and a set of final markings, is an
`NA.FinAcc` whose input symbols are the transitions. Its language is the set of firing sequences
leading from the initial marking to a final marking. When the net is bounded, only finitely many
markings are reachable, so the language is regular.

## Main definitions

- `PetriNet.firingLanguage`: the firing sequences from `M₀` to a final marking.
- `PetriNet.toNAFinAcc`: the automaton on the markings reachable from `M₀`.

## Main statements

- `PetriNet.language_toNAFinAcc`: the language of the automaton is the firing language.
- `PetriNet.isRegular_firingLanguage`: the language of a bounded net over finitely many places is
  regular.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

open Automata

variable {Place Transition : Type} (N : PetriNet Place Transition)

/-- The automaton with the markings reachable from `M₀` as states, `M₀` as initial state, and the
final markings `F` as accepting states. -/
def toNAFinAcc (M₀ : Marking Place) (F : Set (Marking Place)) :
    NA.FinAcc {M // M₀ ⇝[N] M} Transition where
  toLTS := N.lts.generatedBy M₀
  start := {⟨M₀, Reachable.refl N M₀⟩}
  accept := {s | s.1 ∈ F}

/-- The firing language: the sequences of transitions leading from `M₀` to a final marking. -/
def firingLanguage (M₀ : Marking Place) (F : Set (Marking Place)) : Language Transition :=
  {ts | ∃ M ∈ F, N.lts.MTr M₀ ts M}

variable {N}

/-- The language of the automaton is the firing language. -/
theorem language_toNAFinAcc (M₀ : Marking Place) (F : Set (Marking Place)) :
    Acceptor.language (N.toNAFinAcc M₀ F) = N.firingLanguage M₀ F := by
  ext ts
  simp only [Acceptor.mem_language, firingLanguage]
  change _ ↔ ∃ M ∈ F, N.lts.MTr M₀ ts M
  constructor
  · rintro ⟨s, hs, s', hs', h⟩
    have hs0 : s.1 = M₀ := congrArg Subtype.val hs
    refine ⟨s'.1, hs', ?_⟩
    have := (LTS.generatedBy_mTr_iff N.lts).1 h
    rwa [hs0] at this
  · rintro ⟨M, hM, h⟩
    refine ⟨⟨M₀, Reachable.refl N M₀⟩, rfl, ⟨M, ⟨ts, h⟩⟩, hM, ?_⟩
    exact (LTS.generatedBy_mTr_iff N.lts).2 h

/-- The language of a bounded net over finitely many places is regular. -/
theorem isRegular_firingLanguage [Finite Place] {M₀ : Marking Place} (h : N.Bounded M₀)
    (F : Set (Marking Place)) : (N.firingLanguage M₀ F).IsRegular := by
  rw [Language.IsRegular.iff_nfa]
  have : Finite {M // M₀ ⇝[N] M} := h.finite_generatedBy
  exact ⟨_, this, N.toNAFinAcc M₀ F, language_toNAFinAcc M₀ F⟩

end PetriNet

end Cslib
