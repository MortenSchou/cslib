/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.ExecutableAmple
import Cslib.Computability.PetriNets.ExecutableAmpleLTL
import Cslib.Computability.PetriNets.ExecutableStubborn
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

/-! ### The computed stubborn selector -/

/-- The same net as an executable net, with places `0, 1, 2, 3` and transitions `0, 1`. -/
def execNet : ExecPetriNet (Fin 4) (Fin 2) where
  pre | 0 => {0} | 1 => {2}
  post | 0 => {1} | 1 => {3}

/-- The initial marking, with one token in each of the places `0` and `2`. -/
def M₀ : Multiset (Fin 4) := {0, 2}

/-- At `M₀` both transitions are enabled, and the computed stubborn set contains only the least. -/
example : execNet.stubbornFinset M₀ = {0} := by decide +kernel

/-- The computed set is stubborn. -/
example : IsStubborn execNet.toPetriNet (Multiset.toFinsupp M₀) (execNet.stubbornFinset M₀) :=
  ExecPetriNet.stubbornFinset_isStubborn M₀

/-- The full graph has 4 reachable markings. -/
example : (execNet.reachSet M₀ 3).card = 4 := by decide +kernel

/-- The reduced graph has only 3: the marking `{1, 2}` is reached, but `{0, 3}` never is. -/
example : (execNet.reducedReachSet execNet.stubbornFinset M₀ 3).card = 3 := by decide +kernel

/-- The reduced graph still reaches the dead marking. -/
example : ({1, 3} : Multiset (Fin 4)) ∈ execNet.reducedReachSet execNet.stubbornFinset M₀ 3 := by
  decide +kernel

/-! ### Conflicts

Transitions `0` and `1` compete for the token in place `0`, and transition `2` is independent. -/

/-- Two transitions in conflict and a third that is independent of both. -/
def execNet₃ : ExecPetriNet (Fin 5) (Fin 3) where
  pre | 0 => {0} | 1 => {0} | 2 => {3}
  post | 0 => {1} | 1 => {2} | 2 => {4}

/-- The initial marking with a token in the places `0` and `3`. -/
def M₃ : Multiset (Fin 5) := {0, 3}

/-- The seed is the enabled transition with the smallest generated set: transition `2` generates
only itself, whereas transitions `0` and `1` generate each other. -/
example : execNet₃.stubbornFinset M₃ = {2} := by decide +kernel

/-- The full graph has 6 reachable markings. -/
example : (execNet₃.reachSet M₃ 4).card = 6 := by decide +kernel

/-- The reduced graph has only 4: the conflict between `0` and `1` is explored once. -/
example : (execNet₃.reducedReachSet execNet₃.stubbornFinset M₃ 4).card = 4 := by decide +kernel

/-- The level 4 of the reduced graph is closed. -/
example : execNet₃.ReducedClosed execNet₃.stubbornFinset M₃ 4 := by decide +kernel

/-- Both dead markings, resulting from the conflict, remain reachable in the reduced graph. -/
example : {1, 4} ∈ execNet₃.reducedReachSet execNet₃.stubbornFinset M₃ 4 ∧
    {2, 4} ∈ execNet₃.reducedReachSet execNet₃.stubbornFinset M₃ 4 := by decide +kernel

/-- Transitions in conflict. -/
example : execNet₃.toPetriNet.Conflict 0 1 := ExecPetriNet.conflicts_iff.1 (by decide)

/-- The singleton of a transition that is in conflict with another is not closed: selecting only
`0` at `M₃` would lose the dead marking `{2, 4}`. -/
example : ¬ StubbornClosed execNet₃.toPetriNet (Multiset.toFinsupp M₃) {0} := fun h =>
  h.1 0 rfl (ExecPetriNet.enabled_toPetriNet_iff.2 (by decide)) 1 (by decide)
    (ExecPetriNet.conflicts_iff.1 (by decide))

/-- The dead markings of `execNet₃` are reachable iff they are reachable in the reduced graph. -/
example : (∃ D, execNet₃.toPetriNet.Dead D ∧ (Multiset.toFinsupp M₃) ⇝[execNet₃] D) ↔
    ∃ D, execNet₃.toPetriNet.Dead D ∧
      (execNet₃.toPetriNet.reduced execNet₃.stubbornSelector).CanReach (Multiset.toFinsupp M₃) D :=
  ExecPetriNet.canReach_dead_iff_reduced _

/-- A dead marking is reachable in `execNet₃`, hence also in the reduced graph. -/
example : ∃ D, execNet₃.toPetriNet.Dead D ∧
    (execNet₃.toPetriNet.reduced execNet₃.stubbornSelector).CanReach (Multiset.toFinsupp M₃) D := by
  refine (ExecPetriNet.canReach_dead_iff_reduced _).1 ⟨Multiset.toFinsupp {1, 4},
    ExecPetriNet.dead_toFinsupp_iff.2 (by decide),
    ExecPetriNet.reachable_of_mem_reachSet execNet₃ (n := 4) (by decide +kernel)⟩

/-! ### Transitions that only read a shared place do not conflict

Both transitions read the token in place `0` and consume a private token. -/

/-- Transitions `0` and `1` read the place `0`. -/
def execNetR : ExecPetriNet (Fin 5) (Fin 2) where
  pre | 0 => {0, 1} | 1 => {0, 2}
  post | 0 => {0, 3} | 1 => {0, 4}

/-- The initial marking. -/
def MR : Multiset (Fin 5) := {0, 1, 2}

/-- The presets share a place, but the transitions are not in conflict. -/
example : ¬ execNetR.toPetriNet.Conflict 0 1 := fun h => by
  have := ExecPetriNet.conflicts_iff.2 h
  revert this
  decide

/-- The stubborn set at `MR` contains only one of the transitions. -/
example : execNetR.stubbornFinset MR = {0} := by decide +kernel

/-- The full graph has 4 reachable markings. -/
example : (execNetR.reachSet MR 3).card = 4 := by decide +kernel

/-- The reduced graph has 3. -/
example : (execNetR.reducedReachSet execNetR.stubbornFinset MR 3).card = 3 := by decide +kernel

/-! ### Partial-order reduction for safety properties

Here transition `0` moves a token from place `2` to `3` and is invisible, transition `1` moves a
token from place `0` to `1` and is visible. The place invariant `#0 + #1 ≤ 1` is not changed by
the invisible transition. -/

/-- The net with the invisible transition `0` and the visible transition `1`. -/
def execNet₂ : ExecPetriNet (Fin 4) (Fin 2) where
  pre | 0 => {2} | 1 => {0}
  post | 0 => {3} | 1 => {1}

/-- The visible transitions. -/
def vis : Finset (Fin 2) := {1}

/-- The level: the number of tokens in the places `1` and `3`, capped at `2`. Every firing increases
it until it is capped, so no marking in the example is closing. -/
def lvl (M : Multiset (Fin 4)) : ℕ := min 2 (M.count 1 + M.count 3)

/-- The safety property: at most one token in places `0` and `1` together. -/
def Safe (M : Multiset (Fin 4)) : Prop := M.count 0 + M.count 1 ≤ 1

instance (M : Multiset (Fin 4)) : Decidable (Safe M) := inferInstanceAs (Decidable (_ ≤ _))

/-- The full graph has 4 reachable markings. -/
example : (execNet₂.reachSet M₀ 3).card = 4 := by decide +kernel

/-- The reduced graph has 3: the visible transition is not taken at the initial marking. -/
example : (execNet₂.ampleReachSet lvl vis M₀ 3).card = 3 := by decide +kernel

/-- Level `3` of the reduced graph is closed. -/
example : execNet₂.AmpleClosed lvl vis M₀ 3 := by decide +kernel

/-- The safety property holds on the reduced graph. -/
example : ∀ M ∈ execNet₂.ampleReachSet lvl vis M₀ 3, Safe M := by decide +kernel

/-- Hence it holds on all reachable markings of the full net, without a bound on the level. -/
example : ∀ M : Multiset (Fin 4), M₀ ⇝[execNet₂] M → Safe M :=
  ExecPetriNet.forall_reachable_of_ampleReachSet (N := execNet₂) (lvl := lvl) (V := vis)
    (P := Safe)
    (fun M t _ ht => by
      match t, ht with
      | 0, _ => simp [execNet₂, Safe]
      | 1, ht => exact absurd (by decide) ht)
    (n := 3) (by decide +kernel) (by decide +kernel)

/-- When the stubborn set contains an enabled visible transition, all transitions are selected. -/
example : execNet₂.ampleFinset lvl {0} M₀ = Finset.univ := by decide +kernel

/-- With a visible transition that is not in the stubborn set, the stubborn set is selected. -/
example : execNet₂.ampleFinset lvl vis M₀ = {0} := by decide +kernel

/-- The marking is not closing for `lvl`, but it is for a level that never increases. -/
example : ¬ execNet₂.Closing lvl M₀ := by decide +kernel

/-- A constant level makes every marking with an enabled transition closing. -/
example : execNet₂.Closing (fun _ => 0) M₀ ∧
    execNet₂.ampleFinset (fun _ => 0) vis M₀ = Finset.univ := by decide +kernel

/-! ### Partial-order reduction for LTL without next-time -/

/-- The level is bounded by `2` on all markings. -/
theorem levelBounded (M₀ : Marking (Fin 4)) : execNet₂.LevelBounded lvl vis 2 M₀ :=
  fun _ _ => min_le_left _ _

/-- The invisible transition `0` does not change the preset places of the transition `1`, so the
atoms `enabled 1` are not changed by it. -/
theorem visibleOf_subset :
    execNet₂.visibleOf (({1} : Finset (Fin 2)).biUnion fun u => (execNet₂.pre u).toFinset) ⊆
      vis := by
  decide +kernel

/-- The formula `G F (enabled 1)` is preserved by the reduction. -/
example (M₀ : Marking (Fin 4)) :
    Cslib.Logic.LTL.AllPaths execNet₂.model M₀
        (.always (.eventually (.atom (Atom.enabled (1 : Fin 2))))) ↔
      Cslib.Logic.LTL.AllPaths (execNet₂.ampleModel lvl vis) M₀
        (.always (.eventually (.atom (Atom.enabled (1 : Fin 2))))) :=
  ExecPetriNet.allPaths_ampleModel_iff (levelBounded M₀)
    (ExecPetriNet.enabled_atoms_invisible visibleOf_subset)
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
