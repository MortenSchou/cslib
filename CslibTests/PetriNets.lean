/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Basic
import Cslib.Computability.PetriNets.ConflictFree
import Cslib.Computability.PetriNets.PlaceInvariants
import Cslib.Computability.PetriNets.ReachabilityConditions
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
  pre | produce => ⦅producing⦆ | consume => ⦅buffer⦆
  post | produce => ⦅buffer⦆ | consume => ⦅consuming⦆

/-! ### Conflict-free nets -/

theorem prodCons_conflictFree : prodCons.ConflictFree := by
  intro t u p h₁ h₂
  cases t <;> cases u <;> cases p <;> simp_all [prodCons]

example : prodCons.Firable ⦅producing⦆ (Finsupp.single produce 1 + Finsupp.single consume 1) := by
  have h₁ : ⦅producing⦆ [produce⟩[prodCons] ⦅buffer⦆ :=
    ⟨0, by ext p; cases p <;> simp [prodCons],
      by ext p; cases p <;> simp [prodCons]⟩
  have h₂ : ⦅buffer⦆ [consume⟩[prodCons] ⦅consuming⦆ :=
    ⟨0, by ext p; cases p <;> simp [prodCons],
      by ext p; cases p <;> simp [prodCons]⟩
  exact ⟨[produce, consume], ⦅consuming⦆, .stepL h₁ (.single _ h₂), by simp⟩

/-! ### Flow-acyclic nets -/

/-- The producer feeds the consumer but not conversely, so the net is flow-acyclic and its
reachability is decided by the state equation (`FlowAcyclic.reachable_iff`). -/
theorem prodCons_flowAcyclic : prodCons.FlowAcyclic :=
  Subrelation.wf (r := InvImage (· < ·) fun t : Tr => if t = produce then 0 else 1)
    (fun {u t} ⟨p, hu, ht⟩ => by cases u <;> cases t <;> cases p <;> simp_all [prodCons, InvImage])
    (InvImage.wf _ wellFounded_lt)

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

/-! ### The state equation -/

/-- Two items in the system. -/
def M₀ : Marking Pl := ⦅producing, producing⦆

/-- Firing never produces tokens in `producing`. -/
theorem prodCons_incidence_producing (t : Tr) : prodCons.incidence t producing ≤ 0 := by
  cases t <;> simp [incidence, Marking.toInt, prodCons]

theorem prodCons_effect_producing (ts : List Tr) : prodCons.effect ts producing ≤ 0 := by
  induction ts with
  | nil => simp
  | cons t ts ih =>
    rw [effect_cons, Finsupp.add_apply]
    have := prodCons_incidence_producing t
    omega

/-- By the state equation, no marking with more `producing` tokens than `M₀` is reachable. -/
example (M : Marking Pl) (h : 2 < M producing) : ¬ M₀ ⇝[prodCons] M := by
  intro hr
  obtain ⟨ts, hts⟩ := hr.exists_toInt_eq
  have h1 := congrArg (fun f => f producing) hts
  have h2 := prodCons_effect_producing ts
  simp [Marking.toInt, M₀, Multiset.toFinsupp_apply] at h1
  omega

/-! ### Place invariants -/

/-- Two `a` tokens are merged into one `b` token, so `a` has weight `1` and `b` has weight `2`. -/
inductive Pl2 | a | b
  deriving DecidableEq

instance : Fintype Pl2 := ⟨{.a, .b}, fun x => by cases x <;> simp⟩

def merge : PetriNet Pl2 Unit where
  pre _ := ⦅.a, .a⦆
  post _ := ⦅.b⦆

def mergeWeight : Pl2 → ℕ | .a => 1 | .b => 2

theorem merge_invariant : merge.IsInvariant mergeWeight := by
  intro t
  change Marking.weight mergeWeight ⦅.a, .a⦆ = Marking.weight mergeWeight ⦅.b⦆
  rw [Marking.weight_toFinsupp, Marking.weight_toFinsupp]
  simp [mergeWeight]

/-- A positive invariant bounds the net at every marking. -/
example (M₀ : Marking Pl2) : merge.Bounded M₀ :=
  merge_invariant.bounded (by intro p; cases p <;> simp [mergeWeight]) M₀

/-- The merge net is not conservative, although it has an invariant. -/
example : ¬ merge.Conservative := by
  rw [conservative_iff_isInvariant]
  intro h
  have := h ()
  change Marking.weight (fun _ => 1) ⦅Pl2.a, Pl2.a⦆ = Marking.weight (fun _ => 1) ⦅Pl2.b⦆ at this
  rw [Marking.weight_toFinsupp, Marking.weight_toFinsupp] at this
  simp at this

/-! ### Siphons and traps -/

/-- In the producer/consumer net, `producing` is a siphon (nothing produces into it) and
`consuming` is a trap (nothing consumes from it). -/
theorem prodCons_siphon : prodCons.IsSiphon {producing} := by
  rintro t ⟨p, rfl, hpos⟩
  cases t <;> simp [prodCons] at hpos

theorem prodCons_trap : prodCons.IsTrap {consuming} := by
  rintro t ⟨p, rfl, hpos⟩
  cases t <;> simp [prodCons] at hpos

/-- With no `producing` token, none can ever appear. -/
example (M M' : Marking Pl) (h : M ⇝[prodCons] M') (hM : M producing = 0) :
    M' producing = 0 := by
  have := prodCons_siphon.unmarked_of_reachable h (fun ⟨p, hp, hpos⟩ => by
    simp only [Set.mem_singleton_iff] at hp; subst hp; omega)
  by_contra hne
  exact this ⟨producing, rfl, Nat.pos_of_ne_zero hne⟩

/-- A two-place cycle: `false` moves a token from place `false` to place `true`, and `true`
moves it back. -/
def cycleNet : PetriNet Bool Bool where
  pre t := ⦅t⦆
  post t := ⦅!t⦆

theorem cycleNet_ordinary : cycleNet.Ordinary := by
  intro t p
  cases t <;> cases p <;> simp [cycleNet]

/-- The firing sequence `[false, true]` of the cycle net has total effect zero, so it returns to
its starting marking from every marking where it can fire. -/
example (M M' : Marking Bool) (h : cycleNet.lts.MTr M [false, true] M') : M' = M := by
  refine (mTr_eq_iff_effect_eq_zero h).2 ?_
  ext p
  cases p <;> simp [effect, incidence, Marking.toInt, cycleNet]

end CslibTests
