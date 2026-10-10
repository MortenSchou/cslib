/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.BackwardCoverability
import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.Coverability
import Cslib.Computability.PetriNets.CoverabilityBasis
import Cslib.Computability.PetriNets.Executable
import Cslib.Computability.PetriNets.ExecutableBoundedness
import Cslib.Computability.PetriNets.ExecutableCoverability
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

/-! ### Monotonicity -/

theorem fires_produce : ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ :=
  ⟨0, by simp [prodCons], by simp [prodCons]⟩

theorem fires_consume : ⦅buffer⦆ [consume⟩[prodCons] ⦅consuming⦆ :=
  ⟨0, by simp [prodCons], by simp [prodCons]⟩

/-- Extra tokens never disable a transition. -/
example : ⦅producing, consuming⦆ [produce⟩[prodCons] :=
  (show ⦅producing⦆ [produce⟩[prodCons] from le_rfl).mono (by
    intro p; cases p <;> simp [Multiset.toFinsupp_apply])

/-- A firing sequence can be replayed from a larger marking, reaching a larger marking. -/
example : ∃ M', prodCons.lts.MTr ⦅producing, consuming⦆ [produce] M' ∧ ⦅buffer⦆ ≤ M' :=
  mTr_mono (.single _ fires_produce) (by
    intro p; cases p <;> simp [Multiset.toFinsupp_apply])

/-- The net is bounded at every marking, hence at the smaller marking `⦅producing⦆`. -/
example : prodCons.Bounded ⦅producing⦆ :=
  (prodCons_conservative.kBounded _).bounded

/-! ### Coverability and unboundedness -/

/-- A source transition that creates a token from nothing. -/
noncomputable def source : PetriNet Unit Unit where
  pre _ := 0
  post _ := Finsupp.single () 1

theorem source_fires (M : Marking Unit) : M [()⟩[source] (M + Finsupp.single () 1) :=
  ⟨M, by simp [source], by simp [source]⟩

/-- The source net is unbounded, by pumping from the empty marking. -/
theorem source_unbounded : ¬ source.Bounded 0 :=
  not_bounded_of_pump (.refl _ _) (source_fires 0).reachable (by
    simp only [zero_add]
    exact lt_of_le_of_ne bot_le (fun h => by simpa using DFunLike.congr_fun h ()))

/-- By the characterisation of unbounded nets, the source net has a pumping pair. -/
example : ∃ M₁ M₂, 0 ⇝[source] M₁ ∧ M₁ ⇝[source] M₂ ∧ M₁ < M₂ :=
  exists_pump_of_not_bounded source_unbounded

/-- The producer/consumer net is bounded, so no reachable marking can be pumped. -/
example (M₀ : Marking Pl) : ¬ ∃ M₁ M₂, M₀ ⇝[prodCons] M₁ ∧ M₁ ⇝[prodCons] M₂ ∧ M₁ < M₂ :=
  bounded_iff_no_pump.1 (prodCons_conservative.kBounded _).bounded

/-- Every marking is coverable from every marking in the source net. -/
theorem source_coverable (M₀ M : Marking Unit) : source.Coverable M₀ M := by
  have hreach : ∀ n : ℕ, M₀ ⇝[source] (M₀ + n • Finsupp.single () 1) := by
    intro n
    induction n with
    | zero => simpa using Reachable.refl source M₀
    | succ n ih =>
      refine ih.trans (Fires.reachable (t := ()) ?_)
      have := source_fires (M₀ + n • Finsupp.single () 1)
      rwa [succ_nsmul, ← add_assoc]
  exact ⟨_, hreach (M ()), fun u => by simp⟩

/-- Hence every finite basis for coverability on the source net contains the empty marking. -/
example (M : Marking Unit) : ∃ B : Set (Marking Unit), B.Finite ∧ (0 : Marking Unit) ∈ B ∧
    ∀ M₀, source.Coverable M₀ M ↔ ∃ b ∈ B, b ≤ M₀ := by
  obtain ⟨B, hB, hiff⟩ := exists_finite_basis_coverable (N := source) M
  obtain ⟨b, hb, hb0⟩ := (hiff 0).1 (source_coverable 0 M)
  have hb' : b = 0 := le_antisymm hb0 bot_le
  exact ⟨B, hB, hb' ▸ hb, hiff⟩

/-- Backward coverability on the producer/consumer net: `⦅buffer⦆` is a predecessor of the target
`⦅consuming⦆` after one step, and `⦅producing⦆` after two. -/
theorem producing_mem_backSeq : ⦅producing⦆ ∈ prodCons.backSeq ⦅consuming⦆ 2 := by
  have h1 : ⦅buffer⦆ ∈ prodCons.backSeq ⦅consuming⦆ 1 := by
    rw [backSeq_succ]
    exact Or.inr ⟨consume, _, fires_consume, show _ ∈ Set.Ici _ from Set.mem_Ici.2 le_rfl⟩
  rw [backSeq_succ]
  exact Or.inr ⟨produce, _, fires_produce, h1⟩

example : prodCons.Coverable ⦅producing⦆ ⦅consuming⦆ :=
  coverable_of_mem_backSeq producing_mem_backSeq

/-- The backward iteration reaches a fixpoint that is exactly the coverable markings. -/
example : ∃ n, prodCons.backStep (prodCons.backSeq ⦅consuming⦆ n) = prodCons.backSeq ⦅consuming⦆ n ∧
    ∀ M₀, prodCons.Coverable M₀ ⦅consuming⦆ ↔ M₀ ∈ prodCons.backSeq ⦅consuming⦆ n :=
  exists_backSeq_fixpoint _

/-! ### Executable nets

An `ExecPetriNet` has multisets as arc weights, so firing is computable and the properties of the
net can be decided. -/

/-- The producer/consumer net with multisets as arc weights. -/
def prodConsExec : ExecPetriNet Pl Tr where
  pre | produce => {producing} | consume => {buffer}
  post | produce => {buffer} | consume => {consuming}

/-- It is the same net as `prodCons`. -/
example : prodConsExec.toPetriNet = prodCons := by
  have h : ∀ t, prodConsExec.toPetriNet.pre t = prodCons.pre t ∧
      prodConsExec.toPetriNet.post t = prodCons.post t := by
    intro t; cases t <;> exact ⟨rfl, rfl⟩
  cases h₁ : prodConsExec.toPetriNet
  cases h₂ : prodCons
  simp only [PetriNet.mk.injEq]
  constructor <;> funext t <;> [have := (h t).1; have := (h t).2] <;> simp_all

/-- Two items in the system, as a multiset. -/
def Mx : Multiset Pl := {producing, producing}

example : prodConsExec.enabled Mx produce = true := by decide
example : prodConsExec.enabled Mx consume = false := by decide

example : (prodConsExec.run Mx [produce, consume]).isSome = true := by decide
example : (prodConsExec.run Mx [consume]).isNone = true := by decide
example :
    prodConsExec.run Mx [produce, produce, consume] = some ({buffer, consuming} : Multiset Pl) := by
  decide

/-- The computable run is witnessed in the weighted semantics, with the net given to the notation as
an executable net. -/
example : Mx [produce⟩[prodConsExec] ⦅producing, buffer⦆ :=
  ExecPetriNet.fires_iff.2 (by decide)

/-- Enabledness of a transition at a marking given by a multiset. -/
example : ⦅producing⦆ [produce⟩[prodConsExec] :=
  ExecPetriNet.enabled_toPetriNet_iff.2 (by decide)

/-- Reachability and its notation, for an executable net. -/
example : ⦅producing⦆ ⇝[prodConsExec] ⦅consuming⦆ := by
  have h₁ : ⦅producing⦆ [produce⟩[prodConsExec] ⦅buffer⦆ := ExecPetriNet.fires_iff.2 (by decide)
  have h₂ : ⦅buffer⦆ [consume⟩[prodConsExec] ⦅consuming⦆ := ExecPetriNet.fires_iff.2 (by decide)
  exact h₁.reachable.trans h₂.reachable

/-! ### Decidable coverability -/

/-- The backward iteration from `{consuming}` has stabilised after two steps. -/
example : prodConsExec.Stable (prodConsExec.basisSeq {consuming} 2) := by decide

/-- `{producing}` can cover `{consuming}`. -/
example : prodConsExec.toPetriNet.Coverable ⦅producing⦆ ⦅consuming⦆ := by decide

/-- The empty marking cannot cover `{consuming}`. -/
example : ¬ prodConsExec.toPetriNet.Coverable ⦅⦆ ⦅consuming⦆ := by decide

/-! ### Decidable boundedness -/

/-- The reachable markings of the producer/consumer net from `Mx` stop growing after four steps. -/
example : prodConsExec.Closed Mx 4 := by decide

/-- A source transition that creates a token from nothing, as an executable net. -/
def sourceExec : ExecPetriNet Unit Unit where
  pre _ := 0
  post _ := {()}

/-- The source net has a pumping pair already within one step. -/
example : sourceExec.PumpWithin 0 1 := by decide

/-- Boundedness is decided outright, in both directions. -/
example : prodConsExec.toPetriNet.Bounded Mx := by decide

example : ¬ sourceExec.toPetriNet.Bounded ⦅⦆ := by decide

end CslibTests
