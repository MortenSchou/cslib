/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.StubbornSets

namespace CslibTests

open Cslib PetriNet
open scoped PetriNet

namespace StubbornSets

inductive Pl | a | b | c | d
  deriving DecidableEq

inductive Tr | t | u
  deriving DecidableEq

open Pl Tr

/-- Two transitions on disjoint places: `t` moves a token from `a` to `b`, `u` from `c` to `d`. -/
def net : PetriNet Pl Tr where
  pre | t => {a} | u => {c}
  post | t => {b} | u => {d}

/-- The two transitions commute. -/
example : net.Commutes t u := by decide

/-- They are not in conflict. -/
example : ¬ net.Conflict t u := by decide

/-- Disjoint presets rule out a conflict. -/
example : ¬ net.Conflict t u := not_conflict_of_disjoint (by simp [net])

/-- Swapping the commuting transitions preserves the final marking. -/
example : net.lts.MTr {a, c} [t, u] {b, d} ↔ net.lts.MTr {a, c} [u, t] {b, d} :=
  (LTS.SwapStep.swap [] [] (I := net.Commutes) (μ := t) (ν := u) (by decide)).mTr_iff
    net.lts_commutesWith Commutes.symm

/-- The diamond: from `{a, c}`, both orders reach the same marking. -/
example : ∃ M, ({b, c} : Marking Pl) [u⟩[net] M ∧ ({a, d} : Marking Pl) [t⟩[net] M :=
  Fires.diamond (N := net) (M := {a, c}) (t := t) (u := u) (by simp [net]) (by decide)
    (by decide)

/-- `{t}` is structurally stubborn at `{a, c}`, hence a stubborn set there: `t` is enabled and in
conflict with no other transition. -/
example : net.IsStubborn {a, c} {t} := by
  refine StubbornClosed.isStubborn ⟨?_, ?_⟩ <;> rintro _ rfl
  · intro _ v hv
    cases v
    · exact absurd rfl hv
    · decide
  · intro hdis
    exact absurd (by decide) hdis

/-- Two transitions that both consume the token in `a` are in conflict. -/
def net₂ : PetriNet Pl Bool where
  pre _ := {a}
  post | true => {b} | false => {c}

example : net₂.Conflict true false := by decide

end StubbornSets

end CslibTests
