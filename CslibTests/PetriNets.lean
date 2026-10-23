/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.Semantics

namespace CslibTests

open Cslib PetriNet
open scoped PetriNet

/-! A producer/consumer net: `producing --produce--> buffer --consume--> consuming`. -/

inductive Pl | producing | buffer | consuming
  deriving DecidableEq

inductive Tr | produce | consume
  deriving DecidableEq

open Pl Tr

instance : Fintype Pl := ⟨{producing, buffer, consuming}, fun x => by cases x <;> simp⟩

/-- `produce` turns a `producing` token into a `buffer` token; `consume` moves it to `consuming`. -/
def prodCons : PetriNet Pl Tr where
  pre | produce => ⦅producing⦆ | consume => ⦅buffer⦆
  post | produce => ⦅buffer⦆ | consume => ⦅consuming⦆

/-! ### Notation -/

-- Markings given by multiset literals, and the enabling, firing and reachability notation, are
-- pretty-printed with the notation.

/-- info: ⦅producing, buffer⦆ : Pl →₀ ℕ -/
#guard_msgs in
#check (⦅producing, buffer⦆ : Marking Pl)

/-- info: ⦅⦆ : Pl →₀ ℕ -/
#guard_msgs in
#check (⦅⦆ : Marking Pl)

/-- info: ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ : Prop -/
#guard_msgs in
#check ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆

/-- info: ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆ : Prop -/
#guard_msgs in
#check ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆

/-- The preset and postset of `produce`. -/
example : •[prodCons] produce = ⦅producing⦆ := rfl

example : produce •[prodCons] = ⦅buffer⦆ := rfl

/-! ### Enabling and firing -/

example : ⦅producing⦆ [produce⟩[prodCons] := le_rfl

example : ¬ ⦅producing⦆ [consume⟩[prodCons] := by
  intro h
  have := h buffer
  simp [prodCons] at this

/-- Firing moves the token; the tokens not consumed (here the extra `consuming` token) stay. -/
example : ⦅producing, consuming⦆ [produce⟩[prodCons] ⦅buffer, consuming⦆ :=
  ⟨⦅consuming⦆, by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply],
    by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply]⟩

/-- Firing is the explicit rule `M - pre + post`. -/
example : prodCons.fire ⦅producing, consuming⦆ produce = ⦅buffer, consuming⦆ := by
  have h : ⦅producing, consuming⦆ [produce⟩[prodCons] ⦅buffer, consuming⦆ :=
    ⟨⦅consuming⦆, by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply],
    by ext p; cases p <;> simp [prodCons, Multiset.toFinsupp_apply]⟩
  exact (fires_iff.1 h).2.symm

/-! ### Reachability and boundedness -/

example : ⦅producing⦆ ⇝[prodCons] ⦅consuming⦆ := by
  have h₁ : ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ := ⟨0, by simp [prodCons], by simp [prodCons]⟩
  have h₂ : ⦅buffer⦆ [consume⟩[prodCons] ⦅consuming⦆ := ⟨0, by simp [prodCons], by simp [prodCons]⟩
  exact h₁.reachable.trans h₂.reachable

/-- Both transitions consume and produce one token, so the net is conservative. -/
theorem prodCons_conservative : prodCons.Conservative := by
  intro t
  cases t <;> simp [prodCons, Marking.size]

/-- A conservative net is bounded, and with finitely many places it has finitely many reachable
markings. -/
example (M₀ : Marking Pl) : {M | M₀ ⇝[prodCons] M}.Finite :=
  (prodCons_conservative.kBounded M₀).finite_reachable

/-- The marking graph of any net is deterministic. -/
example : prodCons.lts.Deterministic := inferInstance

/-- With finitely many transitions it is finitely branching. -/
instance : Fintype Tr := ⟨{produce, consume}, fun x => by cases x <;> simp⟩

example : prodCons.lts.FinitelyBranching := inferInstance

/-- A marking with no enabled transition is dead. -/
example : prodCons.Dead ⦅consuming⦆ := by
  rw [dead_iff]
  intro t h
  cases t
  · simpa [prodCons] using h producing
  · simpa [prodCons] using h buffer

end CslibTests
