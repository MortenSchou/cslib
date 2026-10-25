/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Decision.AutoReduction

/-! # Soundness need not survive the deletion of a redundant place

A workflow net `N` with a redundant place `a` such that `N` is not sound, but the net `N.removePlace
a` is a sound workflow net. Hence, unlike the fusion of series, the deletion of a redundant place
does not transfer soundness to the original net, and `PetriNet.ReducesWF` has no such rule.

The places `i a b o` are `0, 1, 2, 3`. The transition `split` moves the token of `i` to `a` and
`b`; `skip` moves the token of `b` to `o`; and `join` moves the tokens of `a` and `b` to `o`. The
place `a` always holds at least as many tokens as `b` (it is an implicit place), so it never blocks
`join`. But `skip` leaves the token of `a` behind: the marking `{a, o}` is reachable, so the net is
not sound. Without `a`, the transitions `skip` and `join` are parallel, and the net is sound.
-/

namespace CslibTests.RedundantPlaceSoundness

open Cslib PetriNet

/-- The net. -/
def N : PetriNet (Fin 4) (Fin 3) where
  pre t := (([[0], [2], [1, 2]].getD t.val []) : List (Fin 4))
  post t := (([[1, 2], [3], [3]].getD t.val []) : List (Fin 4))

/-- The net is a workflow net. -/
theorem isWFNet : N.IsWFNet 0 3 := by decide +kernel

/-- The net is not sound: the marking `{a, o}` is reachable. -/
theorem not_sound : ¬ N.Sound 0 3 := by decide +kernel

/-- The place `a` is redundant: it always holds at least as many tokens as `b`. -/
theorem redundant : N.RedundantPlace 1 (token 0) := by
  refine redundantPlace_of_implicit (fun q => if q = 2 then 1 else 0) 0 (by simp) ?_ ?_ ?_
  · simp [Marking.weight_apply, token]
  · intro t
    fin_cases t <;> simp [Marking.weight_apply, N]
  · intro t
    fin_cases t <;> simp [Marking.weight_apply, N]

/-- Without `a`, the net is a workflow net, and it is sound. -/
theorem removePlace_isWFNet_and_sound :
    (N.removePlace 1).IsWFNet ⟨0, by decide +kernel⟩ ⟨3, by decide +kernel⟩ ∧
      (N.removePlace 1).Sound ⟨0, by decide +kernel⟩ ⟨3, by decide +kernel⟩ :=
  ⟨by decide +kernel, by decide +kernel⟩

/-- Soundness of the net with a redundant place deleted does not imply soundness of the net. -/
theorem sound_removePlace_not_sound :
    ∃ (N : PetriNet (Fin 4) (Fin 3)) (p : Fin 4) (hi : (0 : Fin 4) ≠ p) (ho : (3 : Fin 4) ≠ p),
      N.IsWFNet 0 3 ∧ N.RedundantPlace p (token 0) ∧ (N.removePlace p).IsWFNet ⟨0, hi⟩ ⟨3, ho⟩ ∧
        (N.removePlace p).Sound ⟨0, hi⟩ ⟨3, ho⟩ ∧ ¬ N.Sound 0 3 :=
  ⟨N, 1, by decide, by decide, isWFNet, redundant, removePlace_isWFNet_and_sound.1,
    removePlace_isWFNet_and_sound.2, not_sound⟩

end CslibTests.RedundantPlaceSoundness
