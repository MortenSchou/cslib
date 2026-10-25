/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Decision.Ample
import Cslib.Computability.PetriNets.Decision.AmpleLTL
import Cslib.Computability.PetriNets.Decision.Stubborn

namespace CslibTests

open Cslib PetriNet
open scoped PetriNet

namespace StubbornSets

inductive Pl | a | b | c | d
  deriving DecidableEq

inductive Tr | t | u
  deriving DecidableEq

open Pl Tr

/-- The places in the order `a < b < c < d`, for the computed stubborn selector. -/
instance : LinearOrder Pl :=
  LinearOrder.lift' Pl.ctorIdx fun x y h => by cases x <;> cases y <;> first | rfl | cases h

/-- The transitions in the order `t < u`. -/
instance : LinearOrder Tr :=
  LinearOrder.lift' Tr.ctorIdx fun x y h => by cases x <;> cases y <;> first | rfl | cases h

instance : Fintype Tr := ⟨{t, u}, fun x => by cases x <;> simp⟩

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

/-! ### The computed stubborn selector -/

/-- At `{a, c}` both transitions are enabled, and the computed stubborn set contains only the least.
-/
example : net.stubbornFinset {a, c} = {t} := by decide +kernel

/-- The computed set is stubborn. -/
example : net.IsStubborn {a, c} (net.stubbornFinset {a, c}) := stubbornFinset_isStubborn _

/-- The full graph has 4 reachable markings. -/
example : (net.reachSet {a, c} 3).card = 4 := by decide +kernel

/-- The reduced graph has only 3: the marking `{b, c}` is reached, but `{a, d}` never is. -/
example : (net.reducedReachSet net.stubbornFinset {a, c} 3).card = 3 := by decide +kernel

/-- The reduced graph still reaches the dead marking. -/
example : ({b, d} : Marking Pl) ∈ net.reducedReachSet net.stubbornFinset {a, c} 3 := by
  decide +kernel

/-! ### Conflicts

Transitions `0` and `1` compete for the token in place `0`, and transition `2` is independent. -/

/-- Two transitions in conflict and a third that is independent of both. -/
def net₃ : PetriNet (Fin 5) (Fin 3) where
  pre | 0 => {0} | 1 => {0} | 2 => {3}
  post | 0 => {1} | 1 => {2} | 2 => {4}

/-- The initial marking with a token in the places `0` and `3`. -/
def M₃ : Marking (Fin 5) := {0, 3}

/-- The seed is the enabled transition with the smallest generated set: transition `2` generates
only itself, whereas transitions `0` and `1` generate each other. -/
example : net₃.stubbornFinset M₃ = {2} := by decide +kernel

/-- The full graph has 6 reachable markings. -/
example : (net₃.reachSet M₃ 4).card = 6 := by decide +kernel

/-- The reduced graph has only 4: the conflict between `0` and `1` is explored once. -/
example : (net₃.reducedReachSet net₃.stubbornFinset M₃ 4).card = 4 := by decide +kernel

/-- The level 4 of the reduced graph is closed. -/
example : net₃.ReducedClosed net₃.stubbornFinset M₃ 4 := by decide +kernel

/-- Both dead markings, resulting from the conflict, remain reachable in the reduced graph. -/
example : {1, 4} ∈ net₃.reducedReachSet net₃.stubbornFinset M₃ 4 ∧
    {2, 4} ∈ net₃.reducedReachSet net₃.stubbornFinset M₃ 4 := by decide +kernel

/-- Transitions in conflict. -/
example : net₃.Conflict 0 1 := by decide

/-- The singleton of a transition that is in conflict with another is not closed: selecting only
`0` at `M₃` would lose the dead marking `{2, 4}`. -/
example : ¬ StubbornClosed net₃ M₃ {0} := fun h =>
  h.1 0 rfl (by decide) 1 (by decide) (by decide)

/-- The dead markings of `net₃` are reachable iff they are reachable in the reduced graph. -/
example : (∃ D, net₃.Dead D ∧ M₃ ⇝[net₃] D) ↔
    ∃ D, net₃.Dead D ∧ (net₃.reduced (net₃.stubbornFinset ·)).CanReach M₃ D :=
  canReach_dead_iff_reduced_stubbornFinset _

/-- A dead marking is reachable in `net₃`, hence also in the reduced graph. -/
example : ∃ D, net₃.Dead D ∧ (net₃.reduced (net₃.stubbornFinset ·)).CanReach M₃ D :=
  (canReach_dead_iff_reduced_stubbornFinset _).1
    ⟨{1, 4}, dead_iff.2 (by decide), reachable_of_mem_reachSet net₃ (n := 4) (by decide +kernel)⟩

/-! ### Transitions that only read a shared place do not conflict

Both transitions read the token in place `0` and consume a private token. -/

/-- Transitions `0` and `1` read the place `0`. -/
def netR : PetriNet (Fin 5) (Fin 2) where
  pre | 0 => {0, 1} | 1 => {0, 2}
  post | 0 => {0, 3} | 1 => {0, 4}

/-- The initial marking. -/
def MR : Marking (Fin 5) := {0, 1, 2}

/-- The presets share a place, but the transitions are not in conflict. -/
example : ¬ netR.Conflict 0 1 := by decide

/-- The stubborn set at `MR` contains only one of the transitions. -/
example : netR.stubbornFinset MR = {0} := by decide +kernel

/-- The full graph has 4 reachable markings. -/
example : (netR.reachSet MR 3).card = 4 := by decide +kernel

/-- The reduced graph has 3. -/
example : (netR.reducedReachSet netR.stubbornFinset MR 3).card = 3 := by decide +kernel

/-! ### Partial-order reduction for safety properties

Here transition `0` moves a token from place `2` to `3` and is invisible, transition `1` moves a
token from place `0` to `1` and is visible. The place invariant `#0 + #1 ≤ 1` is not changed by
the invisible transition. -/

/-- The net with the invisible transition `0` and the visible transition `1`. -/
def netV : PetriNet (Fin 4) (Fin 2) where
  pre | 0 => {2} | 1 => {0}
  post | 0 => {3} | 1 => {1}

/-- The initial marking, with one token in each of the places `0` and `2`. -/
def M₀ : Marking (Fin 4) := {0, 2}

/-- The visible transitions. -/
def vis : Finset (Fin 2) := {1}

/-- The level: the number of tokens in the places `1` and `3`, capped at `2`. Every firing increases
it until it is capped, so no marking in the example is closing. -/
def lvl (M : Marking (Fin 4)) : ℕ := min 2 (M.count 1 + M.count 3)

/-- The safety property: at most one token in places `0` and `1` together. -/
def AtMostOne (M : Marking (Fin 4)) : Prop := M.count 0 + M.count 1 ≤ 1

instance (M : Marking (Fin 4)) : Decidable (AtMostOne M) := inferInstanceAs (Decidable (_ ≤ _))

/-- The full graph has 4 reachable markings. -/
example : (netV.reachSet M₀ 3).card = 4 := by decide +kernel

/-- The reduced graph has 3: the visible transition is not taken at the initial marking. -/
example : (netV.ampleReachSet lvl vis M₀ 3).card = 3 := by decide +kernel

/-- Level `3` of the reduced graph is closed. -/
example : netV.AmpleClosed lvl vis M₀ 3 := by decide +kernel

/-- The safety property holds on the reduced graph. -/
example : ∀ M ∈ netV.ampleReachSet lvl vis M₀ 3, AtMostOne M := by decide +kernel

/-- Hence it holds on all reachable markings of the full net, without a bound on the level. -/
example : ∀ M, M₀ ⇝[netV] M → AtMostOne M :=
  forall_reachable_of_ampleReachSet (N := netV) (lvl := lvl) (V := vis)
    (fun M t M' h ht => by
      match t, ht with
      | 0, _ =>
        obtain ⟨R, rfl, rfl⟩ := h
        simp [netV, AtMostOne]
      | 1, ht => exact absurd (by decide) ht)
    (n := 3) (by decide +kernel) (by decide +kernel)

/-- When the stubborn set contains an enabled visible transition, all transitions are selected. -/
example : netV.ampleFinset lvl {0} M₀ = Finset.univ := by decide +kernel

/-- With a visible transition that is not in the stubborn set, the stubborn set is selected. -/
example : netV.ampleFinset lvl vis M₀ = {0} := by decide +kernel

/-- The marking is not closing for `lvl`, but it is for a level that never increases. -/
example : ¬ netV.Closing lvl M₀ := by decide +kernel

/-- A constant level makes every marking with an enabled transition closing. -/
example : netV.Closing (fun _ => 0) M₀ ∧
    netV.ampleFinset (fun _ => 0) vis M₀ = Finset.univ := by decide +kernel

/-! ### Partial-order reduction for LTL without next-time -/

/-- The level is bounded by `2` on all markings. -/
theorem levelBounded (M : Marking (Fin 4)) : netV.LevelBounded lvl vis 2 M :=
  fun _ _ => min_le_left _ _

/-- The invisible transition `0` does not change the preset places of the transition `1`, so the
atoms `enabled 1` are not changed by it. -/
theorem visibleOf_subset :
    netV.visibleOf (({1} : Finset (Fin 2)).biUnion fun u => (•[netV] u).toFinset) ⊆ vis := by
  decide +kernel

/-- The formula `G F (enabled 1)` is preserved by the reduction. -/
example (M : Marking (Fin 4)) :
    Cslib.Logic.LTL.AllPaths netV.model M
        (.always (.eventually (.atom (Atom.enabled (1 : Fin 2))))) ↔
      Cslib.Logic.LTL.AllPaths (netV.ampleModel lvl vis) M
        (.always (.eventually (.atom (Atom.enabled (1 : Fin 2))))) :=
  allPaths_ampleModel_iff (levelBounded M) (enabled_atoms_invisible visibleOf_subset)
    (.always (.eventually trivial)) (by
      intro a ha
      refine ⟨1, Finset.mem_singleton_self _, ?_⟩
      rcases ha with h | h
      · exact absurd h (Set.notMem_empty a)
      · rcases h with h | h
        · exact absurd h (Set.notMem_empty a)
        · exact h)

end StubbornSets

end CslibTests
