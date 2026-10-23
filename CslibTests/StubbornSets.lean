/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Independence

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
  pre | t => ⦅a⦆ | u => ⦅c⦆
  post | t => ⦅b⦆ | u => ⦅d⦆

/-- The two transitions commute. -/
example : net.Commutes t u := ⟨by simp [net], by simp [net]⟩

/-- They are not in conflict. -/
example : ¬ net.Conflict t u := not_conflict_of_disjoint (by simp [net])

/-- Swapping the commuting transitions preserves the final marking. -/
example : net.lts.MTr ⦅a, c⦆ [t, u] ⦅b, d⦆ ↔ net.lts.MTr ⦅a, c⦆ [u, t] ⦅b, d⦆ :=
  (LTS.SwapStep.swap [] [] (I := net.Commutes) (μ := t) (ν := u)
    ⟨by simp [net], by simp [net]⟩).mTr_iff net.lts_commutesWith Commutes.symm

/-- The diamond: from `⦅a, c⦆`, both orders reach the same marking. -/
example : ∃ M, ⦅b, c⦆ [u⟩[net] M ∧ ⦅a, d⦆ [t⟩[net] M :=
  Fires.diamond (N := net) (M := ⦅a, c⦆) (t := t) (u := u) (by simp [net])
    ⟨⦅c⦆, by ext p; cases p <;> simp [net], by ext p; cases p <;> simp [net]⟩
    ⟨⦅a⦆, by ext p; cases p <;> simp [net], by ext p; cases p <;> simp [net]⟩

end StubbornSets

end CslibTests
