/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.ExecutableAmplePlaces

namespace CslibTests

open Cslib PetriNet Cslib.Logic Cslib.Logic.LTL
open scoped PetriNet Cslib.Logic.InferenceSystem

namespace AmplePlaces

/-- Transition `0` moves a token from place `2` to place `3`, and transition `1` moves a token from
place `0` to place `1`. They are independent. -/
def net : ExecPetriNet (Fin 4) (Fin 2) where
  pre | 0 => {2} | 1 => {0}
  post | 0 => {3} | 1 => {1}

/-- The initial marking, with a token in each of the places `0` and `2`. -/
def M₀ : Multiset (Fin 4) := {0, 2}

/-- The observed places: only the place `1`. -/
def P : Finset (Fin 4) := {1}

/-- The visible transitions are those that change the place `1`, that is, transition `1`. -/
example : net.visibleOf P = {1} := by decide +kernel

/-- The level: the number of tokens in the places `1` and `3`, capped at `2`. -/
def lvl (M : Multiset (Fin 4)) : ℕ := min 2 (M.count 1 + M.count 3)

/-- The visible transitions. -/
def vis : Finset (Fin 2) := {1}

/-- The full graph has 4 reachable markings. -/
example : (net.reachSet M₀ 3).card = 4 := by decide +kernel

/-- The reduced graph has only 3: the visible transition is not taken at the initial marking. -/
example : (net.ampleReachSet lvl vis M₀ 3).card = 3 := by decide +kernel

/-- Level `3` of the reduced graph is closed. -/
example : net.AmpleClosed lvl vis M₀ 3 := by decide +kernel

/-- The place `1` never holds two tokens in the reduced graph. -/
example : ∀ M ∈ net.ampleReachSet lvl vis M₀ 3, M.count 1 < 2 := by decide +kernel

/-- The level is bounded by `2`. -/
theorem levelBounded (M : Marking (Fin 4)) : net.LevelBounded lvl vis 2 M :=
  fun _ _ => min_le_left _ _

/-- The formula `G ¬(2 ≤ M 1)` has no next-time operator. -/
theorem nextFree : (Formula.always (.not (.atom (⟨1, 2⟩ : PlaceAtom (Fin 4))))).NextFree :=
  .always trivial

/-- `G ¬(2 ≤ M 1)` holds on all maximal firing sequences of the net, since it holds on those of the
reduced graph, which stay in the closed level `3` of the reduced reachable markings. -/
example : ⇓LTL[net.toPetriNet.placeModel,Multiset.toFinsupp M₀ ⊨∀
    Formula.always (.not (.atom ⟨1, 2⟩))] := by
  have hsafe : ∀ m ∈ net.ampleReachSet lvl vis M₀ 3, m.count 1 < 2 := by decide +kernel
  refine (net.allPaths_placeModel_iff (P := P) (levelBounded _) (by decide +kernel)
    nextFree ?_).2 fun f hf h0 => ?_
  · intro a ha
    rcases ha with h | h
    · exact absurd h (Set.notMem_empty a)
    · change a.place ∈ P
      rw [h]
      decide
  · refine Satisfies.always_iff.2 fun k => ?_
    obtain ⟨m, hm, hk⟩ := net.exists_mem_ampleReachSet_of_isPath (n := 3) (lvl := lvl) (V := vis)
      (by decide +kernel) hf h0 k
    have := hsafe m hm
    change ¬ (2 ≤ f (0 + k) 1)
    rw [Nat.zero_add, hk, Multiset.toFinsupp_apply]
    omega

end AmplePlaces

end CslibTests
