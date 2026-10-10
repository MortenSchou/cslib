/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import CslibTests.CTL
import Cslib.Logics.Temporal.LTL.Model
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

end CslibTests.LTL
