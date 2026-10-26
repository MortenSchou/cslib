/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.BackwardCoverability
import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.Coverability
import Cslib.Computability.PetriNets.CoverabilityBasis
import Cslib.Computability.PetriNets.Decision.Boundedness
import Cslib.Computability.PetriNets.Decision.Coverability
import Cslib.Computability.PetriNets.Monotonicity
import Cslib.Computability.PetriNets.Semantics
import Cslib.Computability.PetriNets.Unboundedness

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

/-! ### Monotonicity -/

theorem fires_produce : ({producing} : Marking Pl) [produce⟩[prodCons] {buffer} :=
  ⟨0, rfl, rfl⟩

theorem fires_consume : ({buffer} : Marking Pl) [consume⟩[prodCons] {consuming} :=
  ⟨0, rfl, rfl⟩

/-- Extra tokens never disable a transition. -/
example : ({producing, consuming} : Marking Pl) [produce⟩[prodCons] :=
  (show ({producing} : Marking Pl) [produce⟩[prodCons] from le_rfl).mono (by decide)

/-- A firing sequence can be replayed from a larger marking, reaching a larger marking. -/
example : ∃ M', prodCons.lts.MTr {producing, consuming} [produce] M' ∧ {buffer} ≤ M' :=
  mTr_mono (.single _ fires_produce) (by decide)

/-- The net is bounded at every marking, hence at the smaller marking `{producing}`. -/
example : prodCons.Bounded {producing} :=
  (prodCons_conservative.kBounded _).bounded

/-! ### Coverability and unboundedness -/

/-- A source transition that creates a token from nothing. -/
def source : PetriNet Unit Unit where
  pre _ := 0
  post _ := {()}

theorem source_fires (M : Marking Unit) : M [()⟩[source] (M + {()}) :=
  ⟨M, (zero_add M).symm, rfl⟩

/-- The source net is unbounded, by pumping from the empty marking. -/
theorem source_unbounded : ¬ source.Bounded 0 :=
  not_bounded_of_pump (.refl _ _) (source_fires 0).reachable (Multiset.lt_cons_self 0 ())

/-- By the characterisation of unbounded nets, the source net has a pumping pair. -/
example : ∃ M₁ M₂, 0 ⇝[source] M₁ ∧ M₁ ⇝[source] M₂ ∧ M₁ < M₂ :=
  exists_pump_of_not_bounded source_unbounded

/-- The producer/consumer net is bounded, so no reachable marking can be pumped. -/
example (M₀ : Marking Pl) : ¬ ∃ M₁ M₂, M₀ ⇝[prodCons] M₁ ∧ M₁ ⇝[prodCons] M₂ ∧ M₁ < M₂ :=
  bounded_iff_no_pump.1 (prodCons_conservative.kBounded _).bounded

/-- Every marking is coverable from every marking in the source net. -/
theorem source_coverable (M₀ M : Marking Unit) : source.Coverable M₀ M := by
  have hreach : ∀ n : ℕ, M₀ ⇝[source] (M₀ + n • {()}) := by
    intro n
    induction n with
    | zero => simpa using Reachable.refl source M₀
    | succ n ih =>
      refine ih.trans (Fires.reachable (t := ()) ?_)
      have := source_fires (M₀ + n • {()})
      rwa [succ_nsmul, ← add_assoc]
  refine ⟨_, hreach M.card, ?_⟩
  rw [Multiset.nsmul_singleton, ← Multiset.eq_replicate_card.2 fun _ _ => rfl]
  exact Multiset.le_add_left _ _

/-- Hence every finite basis for coverability on the source net contains the empty marking. -/
example (M : Marking Unit) : ∃ B : Set (Marking Unit), B.Finite ∧ (0 : Marking Unit) ∈ B ∧
    ∀ M₀, source.Coverable M₀ M ↔ ∃ b ∈ B, b ≤ M₀ := by
  obtain ⟨B, hB, hiff⟩ := exists_finite_basis_coverable (N := source) M
  obtain ⟨b, hb, hb0⟩ := (hiff 0).1 (source_coverable 0 M)
  have hb' : b = 0 := Multiset.le_zero.1 hb0
  exact ⟨B, hB, hb' ▸ hb, hiff⟩

/-- Backward coverability on the producer/consumer net: `{buffer}` is a predecessor of the target
`{consuming}` after one step, and `{producing}` after two. -/
theorem producing_mem_backSeq : {producing} ∈ prodCons.backSeq {consuming} 2 := by
  have h1 : {buffer} ∈ prodCons.backSeq {consuming} 1 := by
    rw [backSeq_succ]
    exact Or.inr ⟨consume, _, fires_consume, show _ ∈ Set.Ici _ from Set.mem_Ici.2 le_rfl⟩
  rw [backSeq_succ]
  exact Or.inr ⟨produce, _, fires_produce, h1⟩

example : prodCons.Coverable {producing} {consuming} :=
  coverable_of_mem_backSeq producing_mem_backSeq

/-- The backward iteration reaches a fixpoint that is exactly the coverable markings. -/
example : ∃ n, prodCons.backStep (prodCons.backSeq {consuming} n) = prodCons.backSeq {consuming} n ∧
    ∀ M₀, prodCons.Coverable M₀ {consuming} ↔ M₀ ∈ prodCons.backSeq {consuming} n :=
  exists_backSeq_fixpoint _

/-! ### Computable firing

Markings are multisets, so firing is computable and the properties of the net can be decided. -/

/-- The computable firing function agrees with the firing relation. -/
example : prodCons.fire? {producing} produce = some {buffer} :=
  fire?_eq_some_iff.2 fires_produce

/-- Two items in the system. -/
def M₀ : Marking Pl := {producing, producing}

example : M₀ [produce⟩[prodCons] := by decide
example : ¬ M₀ [consume⟩[prodCons] := by decide

example : (prodCons.run M₀ [produce, consume]).isSome = true := by decide
example : (prodCons.run M₀ [consume]).isNone = true := by decide
example : prodCons.run M₀ [produce, produce, consume] = some {buffer, consuming} := by
  decide

/-- The computable firing function witnesses the firing relation. -/
example : M₀ [produce⟩[prodCons] {producing, buffer} :=
  fire?_eq_some_iff.1 (by decide)

/-- Enabledness and firing are decided directly. -/
example : ({producing} : Marking Pl) [produce⟩[prodCons] := by decide

example : M₀ [produce⟩[prodCons] {producing, buffer} := by decide

/-- Reachability is witnessed by a computed run. -/
example : ({producing} : Marking Pl) ⇝[prodCons] {consuming} :=
  ⟨[produce, consume], run_eq_some_iff.1 (by decide)⟩

/-! ### Decidable coverability -/

/-- The backward iteration from `{consuming}` has stabilised after two steps. -/
example : WSTS.Stable prodCons.predBasis
    (WSTS.basisSeq prodCons.predBasis ({consuming} : Marking Pl) 2) := by decide

/-- `{producing}` can cover `{consuming}`. -/
example : prodCons.Coverable {producing} {consuming} := by decide

/-- The empty marking cannot cover `{consuming}`. -/
example : ¬ prodCons.Coverable 0 {consuming} := by decide

/-! ### Decidable boundedness -/

/-- The reachable markings of the producer/consumer net from `M₀` stop growing after four steps. -/
example : prodCons.Closed M₀ 4 := by decide

/-- The source net has a pumping pair already within one step. -/
example : source.PumpWithin 0 1 := by decide

/-- Boundedness is decided outright, in both directions. -/
example : prodCons.Bounded M₀ := by decide

example : ¬ source.Bounded 0 := by decide

end CslibTests
