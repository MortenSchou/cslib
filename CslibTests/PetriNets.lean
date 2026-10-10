/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Automaton
import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.Equivalence
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

/-! ### Firing languages as automata -/

/-- Two items in the system. -/
def M₀ : Marking Pl := ⦅producing, producing⦆

/-- Every firing language of the (bounded) producer/consumer net is regular. -/
example (F : Set (Marking Pl)) : (prodCons.firingLanguage M₀ F).IsRegular :=
  isRegular_firingLanguage (prodCons_conservative.kBounded _).bounded F

/-- The sequence `produce, produce, consume` leads from `M₀` to `⦅buffer, consuming⦆`. -/
example : [produce, produce, consume] ∈ prodCons.firingLanguage M₀ {⦅buffer, consuming⦆} := by
  refine ⟨⦅buffer, consuming⦆, rfl, ?_⟩
  refine .stepL (μ := produce) (s2 := ⦅producing, buffer⦆) ⟨⦅producing⦆, ?_, ?_⟩
    (.stepL (μ := produce) (s2 := ⦅buffer, buffer⦆) ⟨⦅buffer⦆, ?_, ?_⟩
      (.single _ (show ⦅buffer, buffer⦆ [consume⟩[prodCons] ⦅buffer, consuming⦆ from
        ⟨⦅buffer⦆, ?_, ?_⟩)))
  all_goals ext p; cases p <;> simp [M₀, prodCons, Multiset.toFinsupp_apply]

/-- The sequence `[consume]` is not even firable from `M₀`. -/
example : [consume] ∉ prodCons.firingLanguage M₀ {⦅buffer, consuming⦆} := by
  rintro ⟨M, -, h⟩
  cases h with
  | stepL htr _ =>
    have := (fires_iff.1 htr).1 buffer
    simp [M₀, prodCons, Multiset.toFinsupp_apply] at this

/-! ### Behavioural equivalence -/

/-- A marking with no `producing` and no `buffer` token is dead. -/
theorem prodCons_dead (M : Marking Pl) (h₁ : M producing = 0) (h₂ : M buffer = 0) :
    prodCons.Dead M := by
  rw [dead_iff]
  intro t h
  cases t
  · simpa [prodCons, Multiset.toFinsupp_apply, h₁] using h producing
  · simpa [prodCons, Multiset.toFinsupp_apply, h₂] using h buffer

theorem dead_one : prodCons.Dead ⦅consuming⦆ :=
  prodCons_dead _ (by simp) (by simp)

theorem dead_two : prodCons.Dead ⦅consuming, consuming⦆ :=
  prodCons_dead _ (by simp) (by simp)

open LTS in
/-- The markings with one and with two `consuming` tokens are different but bisimilar. -/
example : ∃ M₁ M₂ : Marking Pl, M₁ ≠ M₂ ∧ (M₁ ~[prodCons.lts] M₂) := by
  refine ⟨⦅consuming⦆, ⦅consuming, consuming⦆, fun h => ?_, bisimilar_of_dead _ dead_one dead_two⟩
  simpa [Multiset.toFinsupp_apply] using DFunLike.congr_fun h consuming

/-- Bisimilar markings have the same traces. -/
example : prodCons.lts.traces ⦅consuming⦆ = prodCons.lts.traces ⦅consuming, consuming⦆ :=
  (bisimilar_iff_traces_eq _ _ _).1 (bisimilar_of_dead _ dead_one dead_two)

open Logic.Modal in
/-- Bisimilar dead markings satisfy the same Hennessy-Milner formulas. -/
example : TheoryEq (HML.Model.mk prodCons.lts (fun _ (_ : Unit) => True)).toModal
    ⦅consuming⦆ ⦅consuming, consuming⦆ :=
  (theoryEq_iff_bisimilar prodCons _ (fun _ _ => Iff.rfl) _ _).2
    (bisimilar_of_dead _ dead_one dead_two)

end CslibTests
