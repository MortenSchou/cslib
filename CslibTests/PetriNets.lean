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
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer} | consume => {consuming}

/-! ### Notation -/

-- Markings are multiset literals; the enabling, firing and reachability notation is
-- pretty-printed with the notation.

/-- info: {producing, buffer} : Marking Pl -/
#guard_msgs in
#check ({producing, buffer} : Marking Pl)

/-- info: 0 : Marking Pl -/
#guard_msgs in
#check (0 : Marking Pl)

/-- info: {producing} [produce⟩[prodCons] {buffer} : Prop -/
#guard_msgs in
#check ({producing} : Marking Pl) [produce⟩[prodCons] {buffer}

/-- info: {producing} ⇝[prodCons] {consuming} : Prop -/
#guard_msgs in
#check ({producing} : Marking Pl) ⇝[prodCons] {consuming}

/-- The preset and postset of `produce`. -/
example : •[prodCons] produce = {producing} := rfl

example : produce •[prodCons] = {buffer} := rfl

/-! ### Enabling and firing -/

example : ({producing} : Marking Pl) [produce⟩[prodCons] := le_rfl

example : ¬ ({producing} : Marking Pl) [consume⟩[prodCons] := by decide

/-- Firing moves the token; the tokens not consumed (here the extra `consuming` token) stay. -/
theorem fires_produce_consuming :
    ({producing, consuming} : Marking Pl) [produce⟩[prodCons] {buffer, consuming} :=
  ⟨{consuming}, rfl, Multiset.cons_swap ..⟩

/-- Firing is the explicit rule `M - pre + post`. -/
example : prodCons.fire {producing, consuming} produce = {buffer, consuming} :=
  (fires_iff.1 fires_produce_consuming).2.symm

/-! ### Reachability and boundedness -/

example : ({producing} : Marking Pl) ⇝[prodCons] {consuming} := by
  have h₁ : ({producing} : Marking Pl) [produce⟩[prodCons] {buffer} := by decide
  have h₂ : ({buffer} : Marking Pl) [consume⟩[prodCons] {consuming} := by decide
  exact h₁.reachable.trans h₂.reachable

/-- Both transitions consume and produce one token, so the net is conservative. -/
theorem prodCons_conservative : prodCons.Conservative := by
  intro t
  cases t <;> rfl

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
example : prodCons.Dead {consuming} := by
  rw [dead_iff]
  decide

/-! ### The computable firing rule -/

example : prodCons.fire? {producing} consume = none := by decide

example : prodCons.run {producing} [produce, consume] = some {consuming} := by decide

/-- A run of the computable rule is a firing sequence of the marking graph. -/
example : prodCons.lts.MTr {producing} [produce, consume] {consuming} :=
  run_eq_some_iff.1 (by decide)

/-! ### Firing languages as automata -/

/-- Two items in the system. -/
def M₀ : Marking Pl := {producing, producing}

/-- Every firing language of the (bounded) producer/consumer net is regular. -/
example (F : Set (Marking Pl)) : (prodCons.firingLanguage M₀ F).IsRegular :=
  isRegular_firingLanguage (prodCons_conservative.kBounded _).bounded F

/-- The sequence `produce, produce, consume` leads from `M₀` to `{buffer, consuming}`. -/
example : [produce, produce, consume] ∈ prodCons.firingLanguage M₀ {{buffer, consuming}} := by
  have h₁ : M₀ [produce⟩[prodCons] {producing, buffer} := by decide
  have h₂ : ({producing, buffer} : Marking Pl) [produce⟩[prodCons] {buffer, buffer} := by decide
  have h₃ : ({buffer, buffer} : Marking Pl) [consume⟩[prodCons] {buffer, consuming} := by decide
  exact ⟨_, rfl, .stepL h₁ (.stepL h₂ (.single _ h₃))⟩

/-- The sequence `[consume]` is not even firable from `M₀`. -/
example : [consume] ∉ prodCons.firingLanguage M₀ {{buffer, consuming}} := by
  rintro ⟨M, -, h⟩
  cases h with
  | stepL htr _ => exact absurd (fires_iff.1 htr).1 (by decide)

/-! ### Behavioural equivalence -/

/-- A marking with no `producing` and no `buffer` token is dead. -/
theorem prodCons_dead (M : Marking Pl) (h₁ : producing ∉ M) (h₂ : buffer ∉ M) :
    prodCons.Dead M := by
  rw [dead_iff]
  intro t h
  cases t
  · exact h₁ (Multiset.mem_of_le h (Multiset.mem_singleton_self _))
  · exact h₂ (Multiset.mem_of_le h (Multiset.mem_singleton_self _))

theorem dead_one : prodCons.Dead {consuming} :=
  prodCons_dead _ (by simp) (by simp)

theorem dead_two : prodCons.Dead {consuming, consuming} :=
  prodCons_dead _ (by simp) (by simp)

open LTS in
/-- The markings with one and with two `consuming` tokens are different but bisimilar. -/
example : ∃ M₁ M₂ : Marking Pl, M₁ ≠ M₂ ∧ (M₁ ~[prodCons.lts] M₂) :=
  ⟨{consuming}, {consuming, consuming}, by decide, bisimilar_of_dead _ dead_one dead_two⟩

/-- Bisimilar markings have the same traces. -/
example : prodCons.lts.traces {consuming} = prodCons.lts.traces {consuming, consuming} :=
  (bisimilar_iff_traces_eq _ _ _).1 (bisimilar_of_dead _ dead_one dead_two)

open Logic.Modal in
/-- Bisimilar dead markings satisfy the same Hennessy-Milner formulas. -/
example : TheoryEq (HML.Model.mk prodCons.lts (fun _ (_ : Unit) => True)).toModal
    {consuming} {consuming, consuming} :=
  (theoryEq_iff_bisimilar prodCons _ (fun _ _ => Iff.rfl) _ _).2
    (bisimilar_of_dead _ dead_one dead_two)

end CslibTests
