/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import CslibTests.CTL
import Cslib.Logics.Temporal.LTL.Bisimulation
import Cslib.Logics.Temporal.LTL.Model
import Cslib.Logics.Temporal.LTL.ModelChecking
import Cslib.Logics.Temporal.LTL.OmegaRegular
import Cslib.Logics.Temporal.LTL.SafetyLiveness

namespace CslibTests.LTL

open Cslib Cslib.ωSequence
open Cslib.Logic Cslib.Logic.LTL CslibTests.CTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.LTL.Formula

/-! ## Words

An ω-word is a sequence of sets of atoms. -/

/-- The word that is `{true}` at even positions and `{false}` at odd ones. -/
def alternating : ωSequence (Set Bool) := ⟨fun n => if n % 2 = 0 then {true} else {false}⟩

local notation "a" => (Formula.atom true : Formula Bool)
local notation "b" => (Formula.atom false : Formula Bool)

example : ⇓LTL[alternating ⊨ a] := by simp [alternating]

example : ⇓LTL[alternating ⊨ X b] := by simp [alternating, ωSequence.tail]

example : ¬ ⇓LTL[alternating ⊨ G a] := by
  rw [Satisfies.always_iff]
  intro h
  simpa [alternating] using h 1

/-- `F` and `G` mix: the word visits `b` infinitely often. -/
example : ⇓LTL[alternating ⊨ G F b] := by
  rw [Satisfies.always_iff]
  intro n
  rw [Satisfies.eventually_iff]
  refine ⟨(n + 1) % 2, ?_⟩
  rw [Cslib.Logic.LTL.drop_drop, Satisfies.atom_iff]
  have : ((n + 1) % 2 + n) % 2 = 1 := by omega
  change false ∈ alternating (0 + ((n + 1) % 2 + n))
  simp [alternating, this]

/-- `U`: `a` holds until `b`. -/
example : ⇓LTL[alternating ⊨ a U b] := by
  rw [Satisfies.until_iff]
  refine ⟨1, by simp [alternating], fun k hk => ?_⟩
  obtain rfl : k = 0 := by omega
  simp [alternating]

/-- The unfolding law of `U`. -/
example : ⇓LTL[alternating ⊨ a U b] ↔
    ⇓LTL[alternating ⊨ b] ∨ (⇓LTL[alternating ⊨ a] ∧ ⇓LTL[alternating.tail ⊨ a U b]) :=
  Satisfies.until_unfold

/-! ## Safety and liveness -/

/-- `G ¬b` is a state formula under `G`, hence a safety property. -/
example : (G (¬b)).language.IsSafety :=
  isSafety_language_G trivial

/-- `F b` is satisfiable, hence a liveness property. -/
example : (F b).language.IsLiveness :=
  isLiveness_language_F ⟨⟨fun _ => {false}⟩, by simp⟩

/-! ## Models

An LTL formula holds on a model along maximal paths; CTL formulas are path quantifiers over LTL
formulas over the CTL formulas as atoms. -/

local notation "stop" => (CTL.Formula.atom false : CTL.Formula Bool)

/-- `EF stop` at the start of the lasso is some path satisfying `F stop`. -/
example : ⇓LTL[lasso.lift,0 ⊨∃ F (.atom stop)] :=
  ef_iff_somePath.1 lasso_ef_stop

/-- A formula holds on all paths iff its negation holds on none. -/
example (m : CTL.Model (Fin 4) Bool) (s : Fin 4) (φ : Formula Bool) :
    ⇓LTL[m,s ⊨∀ φ] ↔ ¬ ⇓LTL[m,s ⊨∃ ¬φ] :=
  allPaths_iff_not_somePath

/-! ## Model checking the lasso

Paths from state `0` go around the lp `1 ↔ 2` forever, or leave it for the deadlock `3`, where
they stay forever. -/

local notation "lp" => (Formula.atom true : Formula Bool)
local notation "sp" => (Formula.atom false : Formula Bool)

/-- The deadlock is reachable on some path but not on all of them. -/
example : ⇓LTL[lasso,0 ⊨∃ F sp] := by decide

example : ¬ ⇓LTL[lasso,0 ⊨∀ F sp] := by decide

/-- Every path eventually stays in the lp forever, or reaches the deadlock. This mixes `F` and `G`
in a way that CTL cannot express. -/
example : ⇓LTL[lasso,0 ⊨∀ (F G lp) ∨ (F sp)] := by decide

/-- Some path visits the lp infinitely often, but not all do. -/
example : ⇓LTL[lasso,0 ⊨∃ G F lp] := by decide

example : ¬ ⇓LTL[lasso,0 ⊨∀ G F lp] := by decide

/-- Staying in the lp forever and reaching the deadlock exclude each other. -/
example : ¬ ⇓LTL[lasso,0 ⊨∃ (G lp) ∧ (F sp)] := by decide

/-- `X` looks one step ahead, and the deadlock repeats itself. -/
example : ⇓LTL[lasso,0 ⊨∀ X lp] := by decide

example : ¬ ⇓LTL[lasso,0 ⊨∀ X X lp] := by decide

example : ⇓LTL[lasso,3 ⊨∀ G sp] := by decide

/-- `U`: the lp holds until the deadlock, on the paths that reach it. -/
example : ⇓LTL[lasso,1 ⊨∃ lp U sp] := by decide

example : ¬ ⇓LTL[lasso,1 ⊨∀ lp U sp] := by decide

/-! ## Model checking mutual exclusion -/

/-- Safety: both processes are never critical at once. -/
example : ⇓LTL[mutex true,(0, 0) ⊨∀ G (¬(.atom 0 ∧ .atom 1))] := by decide

example : ¬ ⇓LTL[mutex false,(0, 0) ⊨∀ G (¬(.atom 0 ∧ .atom 1))] := by decide

/-- Without fairness, a process may never get to run: it is not guaranteed to be critical. -/
example : ¬ ⇓LTL[mutex true,(0, 0) ⊨∀ F (.atom 0 : Formula (Fin 2))] := by decide

/-- But the first process is critical infinitely often on some path. -/
example : ⇓LTL[mutex true,(0, 0) ⊨∃ G F (.atom 0 : Formula (Fin 2))] := by decide

/-! ## ω-regularity

The language of an LTL formula is ω-regular, hence so are the languages
obtained from it by the closure properties of ω-regular languages, such as complement, which is
not an LTL operation on formulas of this form. -/

open Cslib in
/-- The sequences in which the first process is not critical infinitely often form an ω-regular
language. -/
example : ((G F (.atom 0 : Formula (Fin 2))).language)ᶜ.IsRegular :=
  ωLanguage.IsRegular.compl (Formula.isRegular_language _)

end CslibTests.LTL
