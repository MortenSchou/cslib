/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Logics.Temporal.CTL.Denotation
import Cslib.Logics.Temporal.CTL.Modal
import Cslib.Logics.Temporal.CTL.Reachability
import Mathlib.Tactic.FinCases

namespace CslibTests.CTL

open Cslib.Logic Cslib.Logic.CTL
open scoped Cslib.Logic.InferenceSystem Cslib.Logic.CTL.Formula

/-! ## A lasso

State `0` enters a loop `1 → 2 → 1`, from which state `3`, a deadlock, can be reached. Atom `true`
holds in the loop and atom `false` holds in the deadlock. -/

def lasso : Model (Fin 4) Bool :=
  .ofRel (fun s t => (s = 0 ∧ t = 1) ∨ (s = 1 ∧ t = 2) ∨ (s = 2 ∧ t = 1) ∨ (s = 1 ∧ t = 3))
    (fun s b => if b then s = 1 ∨ s = 2 else s = 3)

local notation "loop" => (Formula.atom true : Formula Bool)
local notation "stop" => (Formula.atom false : Formula Bool)

/-- Only state `3` is a deadlock. -/
example : ⇓CTL[lasso,3 ⊨ Formula.deadlock] := by
  rw [Satisfies.deadlock_iff]
  intro t h
  fin_cases t <;> simp [lasso] at h

example : ¬ ⇓CTL[lasso,1 ⊨ Formula.deadlock] := by
  rw [Satisfies.deadlock_iff]
  exact fun h => h 2 (by simp [lasso])

/-- The deadlock is reachable from the start. -/
theorem lasso_ef_stop : ⇓CTL[lasso,0 ⊨ EF stop] := by
  rw [Satisfies.ef_iff_reachable]
  refine ⟨3, .head (b := 1) (by simp [lasso]) (.single (by simp [lasso])), ?_⟩
  simp [lasso]

/-- But the state `0` itself does not satisfy `AG loop`. -/
example : ¬ ⇓CTL[lasso,0 ⊨ AG loop] := by
  rw [Satisfies.ag_iff_reachable]
  intro h
  simpa [lasso] using h 0 .refl

/-- The only successor of `0` is `1`, which is in the loop. -/
example : ⇓CTL[lasso,0 ⊨ AX loop] := by
  rw [Satisfies.ax_iff]
  intro t h
  fin_cases t <;> simp [lasso] at h ⊢

/-- The loop can be followed forever, by a maximal path that alternates between `1` and `2`. -/
example : ⇓CTL[lasso,1 ⊨ EG loop] := by
  rw [Satisfies.eg_iff]
  refine ⟨fun n => if n % 2 = 0 then 1 else 2, fun n => Or.inl ?_, by simp, fun n => ?_⟩
  · rcases Nat.mod_two_eq_zero_or_one n with h | h
    · have : (n + 1) % 2 = 1 := by omega
      simp [lasso, h, this]
    · have : (n + 1) % 2 = 0 := by omega
      simp [lasso, h, this]
  · rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [lasso, h]

/-- The fixpoint semantics agrees with the path semantics. -/
example : (3 : Fin 4) ∈ denote lasso Formula.deadlock := by
  rw [mem_denote_iff, Satisfies.deadlock_iff]
  intro t h
  fin_cases t <;> simp [lasso] at h

end CslibTests.CTL
