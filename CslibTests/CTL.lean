/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Logics.Temporal.CTL.Bisimulation
import Cslib.Logics.Temporal.CTL.Denotation
import Cslib.Logics.Temporal.CTL.ModelChecking
import Cslib.Logics.Temporal.CTL.Modal
import Cslib.Logics.Temporal.CTL.Reachability
import Mathlib.Data.Fintype.Prod
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

instance : DecidableRel lasso.tr := fun s t => inferInstanceAs (Decidable ((s = 0 ∧ t = 1) ∨ _))

instance (s : Fin 4) (b : Bool) : Decidable (lasso.v s b) :=
  inferInstanceAs (Decidable (if b then s = 1 ∨ s = 2 else s = 3))


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
example : ⇓CTL[lasso,0 ⊨ EF stop] := by
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

/-- But not on all paths: the loop can be followed forever. -/
example : ¬ ⇓CTL[lasso,0 ⊨ AF stop] := by decide

/-- The deadlock stays reachable from everywhere. -/
example : ⇓CTL[lasso,0 ⊨ AG (EF stop)] := by decide

example : ⇓CTL[lasso,1 ⊨ EG loop] := by decide

example : ¬ ⇓CTL[lasso,0 ⊨ AG loop] := by decide

example : ⇓CTL[lasso,1 ⊨ E[loop U stop]] := by decide

example : ¬ ⇓CTL[lasso,1 ⊨ A[loop U stop]] := by decide

/-- Only state `3` is a deadlock. -/
example : ⇓CTL[lasso,3 ⊨ Formula.deadlock] ∧ ¬ ⇓CTL[lasso,1 ⊨ Formula.deadlock] := by decide

/-- Maximal paths stay forever in a deadlock, so `EG` holds there when the atom does. -/
example : ⇓CTL[lasso,3 ⊨ EG stop] ∧ ¬ ⇓CTL[lasso,3 ⊨ EG loop] := by decide


/-! ## Mutual exclusion

Two processes cycle through idle, trying and critical. With the guard, a process enters its critical
section only if the other is not there. Without it, both can be critical at once. -/

/-- Local states: `0` idle, `1` trying, `2` critical. -/
abbrev Two := Fin 3 × Fin 3

abbrev step (guard : Bool) (s t : Two) : Prop :=
  (t.2 = s.2 ∧ t.1 = s.1 + 1 ∧ (s.1 ≠ 1 ∨ guard = false ∨ s.2 ≠ 2)) ∨
  (t.1 = s.1 ∧ t.2 = s.2 + 1 ∧ (s.2 ≠ 1 ∨ guard = false ∨ s.1 ≠ 2))

def mutex (guard : Bool) : Model Two (Fin 2) :=
  .ofRel (step guard) (fun s i => if i = 0 then s.1 = 2 else s.2 = 2)

instance (g : Bool) : DecidableRel (mutex g).tr := fun s t =>
  inferInstanceAs (Decidable (step g s t))

instance (g : Bool) (s : Two) (i : Fin 2) : Decidable ((mutex g).v s i) :=
  inferInstanceAs (Decidable (if i = 0 then s.1 = 2 else s.2 = 2))

local notation "crit₁" => (Formula.atom 0 : Formula (Fin 2))
local notation "crit₂" => (Formula.atom 1 : Formula (Fin 2))

/-- Safety: the guarded system never has both processes critical. -/
example : ⇓CTL[mutex true,(0, 0) ⊨ AG (¬(crit₁ ∧ crit₂))] := by decide

/-- The unguarded system violates it. -/
example : ¬ ⇓CTL[mutex false,(0, 0) ⊨ AG (¬(crit₁ ∧ crit₂))] := by decide

set_option maxRecDepth 4000 in
/-- A process can always eventually become critical... -/
example : ⇓CTL[mutex true,(0, 0) ⊨ AG (EF crit₁)] := by decide

/-- ...but without fairness it is not guaranteed to, since the other process can run forever. -/
example : ¬ ⇓CTL[mutex true,(0, 0) ⊨ AF crit₁] := by decide

/-! ## Bisimulation

Bisimilar states satisfy the same CTL formulas. Two uses: transferring a property from a small
model to a bigger bisimilar one, and distinguishing states by a formula to show that they are not
bisimilar. -/

section Bisimulation

open Cslib Cslib.LTS

/-- One state with a step to itself. -/
def loop1 : LTS Unit Unit := ⟨fun _ _ _ => True⟩

/-- Two states stepping to each other. -/
def cycle2 : LTS (Fin 2) Unit := ⟨fun s _ t => t = s + 1⟩

/-- A path of three states ending in a deadlock. -/
def path3 : LTS (Fin 3) Unit := ⟨fun s _ t => s.val + 1 = t.val⟩

abbrev noAtoms {S : Type} : S → Empty → Prop := fun _ => nofun

/-- The models of the LTSs, without atoms. -/
def loop1Model : Model Unit Empty := ⟨loop1, noAtoms⟩

def cycle2Model : Model (Fin 2) Empty := ⟨cycle2, noAtoms⟩

def path3Model : Model (Fin 3) Empty := ⟨path3, noAtoms⟩

instance : DecidableRel loop1Model.tr := fun _ _ => inferInstanceAs (Decidable (∃ _ : Unit, True))

instance : DecidableRel cycle2Model.tr := fun s t =>
  inferInstanceAs (Decidable (∃ _ : Unit, t = s + 1))

instance : DecidableRel path3Model.tr := fun s t =>
  inferInstanceAs (Decidable (∃ _ : Unit, s.val + 1 = t.val))

instance {S : Type} (m : Model S Empty) (s : S) (p : Empty) : Decidable (m.v s p) := nomatch p

/-- The loop and the two-cycle are bisimilar. -/
theorem loop1_bisimilar (s : Unit) (t : Fin 2) : Bisimilarity loop1 cycle2 s t :=
  ⟨fun _ _ => True, trivial, fun _ t _ _ =>
    ⟨fun _ _ => ⟨t + 1, rfl, trivial⟩, fun _ _ => ⟨(), trivial, trivial⟩⟩⟩

/-- Atoms play no role here. -/
theorem noAtoms_iff {S₁ S₂ : Type} (s : S₁) (t : S₂) : ∀ p : Empty, noAtoms s p ↔ noAtoms t p :=
  nofun

/-- The one-state model never deadlocks, so neither does the bisimilar two-cycle. -/
example : ⇓CTL[cycle2Model,0 ⊨ AG (¬Formula.deadlock)] :=
  (Satisfies.of_bisimilar (lts₁ := loop1) (v₁ := noAtoms) (v₂ := noAtoms)
    (fun s t _ => noAtoms_iff s t) (loop1_bisimilar () 0) _).1
    (show ⇓CTL[loop1Model,() ⊨ AG (¬Formula.deadlock)] by decide)

/-- A deadlock distinguishes states of the path, so they are not bisimilar. -/
example : ¬ Bisimilarity path3 path3 1 2 := fun h => by
  have : ⇓CTL[path3Model,1 ⊨ Formula.deadlock] ↔ ⇓CTL[path3Model,2 ⊨ Formula.deadlock] :=
    Satisfies.of_bisimilar (v₁ := noAtoms) (v₂ := noAtoms) (fun s t _ => noAtoms_iff s t) h
      Formula.deadlock
  revert this
  decide

end Bisimulation

end CslibTests.CTL
