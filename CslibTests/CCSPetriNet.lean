/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Languages.CCS.PetriNet

namespace CslibTests

open Cslib Cslib.CCS Cslib.CCS.Process

/-! The CCS process `a.0 | ā.0` has two tokens, and its communication is one net transition. -/

abbrev noDefs : Unit → Option (Process Bool Unit) := fun _ => none

abbrev sender : Process Bool Unit := pre (Act.name true) nil

abbrev receiver : Process Bool Unit := pre (Act.coname true) nil

abbrev system : Process Bool Unit := par sender receiver

example : leaves system = {sender, receiver} := rfl

/-- The communication of the system is a `τ`-step of its marking, found through the bisimulation
from the CCS step. -/
example : ∃ M, (netLts noDefs).Tr (leaves system) Act.τ M ∧
    M = leaves (par nil nil) :=
  (isBisimulation_leaves (defs := noDefs) rfl Act.τ).1 (par nil nil) (.com .nc .pre .pre)

/-- The communication as a net transition, fired by the computable firing rule. -/
example : (net noDefs).fire? (leaves system)
    (.comm sender receiver _ _ nil nil .nc .pre .pre) = some (leaves (par nil nil)) := by
  decide

/-- Conversely, the sender alone can fire its action from the marking, leaving the receiver's
token untouched: the net sees the two components as independent. -/
example : ∃ p', (lts (defs := noDefs)).Tr system (Act.name true) p' ∧
    leaves p' = leaves (par nil receiver) := by
  obtain ⟨p', hp', hl⟩ := tr_of_leaves (defs := noDefs) system
    (s := sender) (s' := nil) (R := {receiver}) (μ := Act.name true)
    (by simp [leaves]) .pre
  exact ⟨p', hp', hl.trans (add_comm _ _)⟩

end CslibTests
