/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.PlaceInvariants
import Cslib.Computability.PetriNets.Semantics
import Cslib.Computability.PetriNets.StateEquation
import Cslib.Computability.PetriNets.Structure

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

/-! ### The state equation -/

/-- Two items in the system. -/
def M₀ : Marking Pl := {producing, producing}

/-- Firing never produces tokens in `producing`. -/
theorem prodCons_incidence_producing (t : Tr) : prodCons.incidence t producing ≤ 0 := by
  cases t <;> decide

theorem prodCons_effect_producing (ts : List Tr) : prodCons.effect ts producing ≤ 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [effect_cons, Pi.add_apply]
    have := prodCons_incidence_producing t
    omega

/-- By the state equation, no marking with more `producing` tokens than `M₀` is reachable. -/
example (M : Marking Pl) (h : 2 < M.count producing) : ¬ M₀ ⇝[prodCons] M := by
  intro hr
  obtain ⟨ts, hts⟩ := hr.exists_toInt_eq
  have h1 := congrFun hts producing
  have h2 := prodCons_effect_producing ts
  simp only [Pi.add_apply, Marking.toInt_apply] at h1
  have h3 : M₀.count producing = 2 := rfl
  omega

/-! ### Place invariants -/

/-- Two `a` tokens are merged into one `b` token, so `a` has weight `1` and `b` has weight `2`. -/
inductive Pl2 | a | b
  deriving DecidableEq

instance : Fintype Pl2 := ⟨{.a, .b}, fun x => by cases x <;> simp⟩

def merge : PetriNet Pl2 Unit where
  pre _ := {.a, .a}
  post _ := {.b}

def mergeWeight : Pl2 → ℕ | .a => 1 | .b => 2

theorem merge_invariant : merge.IsInvariant mergeWeight := by
  intro t
  rw [Marking.weight_apply, Marking.weight_apply]
  rfl

/-- A positive invariant bounds the net at every marking. -/
example (M₀ : Marking Pl2) : merge.Bounded M₀ :=
  merge_invariant.bounded (by intro p; cases p <;> simp [mergeWeight]) M₀

/-- The merge net is not conservative, although it has an invariant. -/
example : ¬ merge.Conservative := by
  rw [conservative_iff_isInvariant]
  intro h
  exact absurd (h ()) (by decide)

/-! ### Siphons and traps -/

/-- In the producer/consumer net, `producing` is a siphon (nothing produces into it) and
`consuming` is a trap (nothing consumes from it). -/
theorem prodCons_siphon : prodCons.IsSiphon {producing} := by
  rintro t ⟨p, rfl, hp⟩
  cases t <;> simp [prodCons] at hp

theorem prodCons_trap : prodCons.IsTrap {consuming} := by
  rintro t ⟨p, rfl, hp⟩
  cases t <;> simp [prodCons] at hp

/-- With no `producing` token, none can ever appear. -/
example (M M' : Marking Pl) (h : M ⇝[prodCons] M') (hM : producing ∉ M) :
    producing ∉ M' := fun hp =>
  prodCons_siphon.unmarked_of_reachable h (fun ⟨_, rfl, hpM⟩ => hM hpM) ⟨producing, rfl, hp⟩

/-- A two-place cycle: `false` moves a token from place `false` to place `true`, and `true`
moves it back. -/
def cycleNet : PetriNet Bool Bool where
  pre t := {t}
  post t := {!t}

theorem cycleNet_ordinary : cycleNet.Ordinary :=
  fun t => ⟨Multiset.nodup_singleton t, Multiset.nodup_singleton !t⟩

/-- The firing sequence `[false, true]` of the cycle net has total effect zero, so it returns to
its starting marking from every marking where it can fire. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M :=
  (mTr_eq_iff_effect_eq_zero h).2 (by decide)

/-- The same, by the multiset form of the state equation: the sequence consumes exactly the
tokens it produces. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M :=
  (mTr_eq_iff_sum_pre_eq h).2 (by decide)

end CslibTests
