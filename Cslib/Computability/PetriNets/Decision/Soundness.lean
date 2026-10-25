/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Decision.Boundedness
public import Cslib.Computability.PetriNets.Decision.Reachability
public import Cslib.Computability.PetriNets.Soundness

/-! # Checking soundness of workflow nets

Soundness of a net with source `i` and sink `o` is decidable over finitely many places and
transitions. A sound net is bounded, so a pumping pair from `{i}` shows unsoundness. Otherwise a
closed level `n` of the markings reachable from `{i}` contains all reachable markings, and soundness
reduces to three checks on that level: markings with a token in the sink are the final marking,
every transition is enabled somewhere, and the final marking is reachable from every marking of the
level. The last check uses `PetriNet.decidableReachable`.

## Main definitions

- `PetriNet.decidableSound`: the decision procedure for soundness.

## Main statements

- `PetriNet.sound_iff_checks`: soundness at a closed level is the three finite checks.
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  {N : PetriNet Place Transition}

/-- On a closed level of the markings reachable from `{i}`, soundness is a finite check, apart from
the reachability of the final marking from each marking of the level. -/
theorem sound_iff_checks {i o : Place} {n : ℕ} (hc : N.Closed (token i) n) :
    N.Sound i o ↔ (∀ M ∈ N.reachSet (token i) n, token o ≤ M → M = token o) ∧
      (∀ t, ∃ M ∈ N.reachSet (token i) n, M [t⟩[N]) ∧
      ∀ M ∈ N.reachSet (token i) n, M ⇝[N] token o := by
  simp only [← reachable_iff_mem_reachSet hc]
  exact ⟨fun h => ⟨h.proper, h.noDead, h.completion⟩, fun ⟨hp, hd, hcomp⟩ => ⟨hcomp, hp, hd⟩⟩

variable [Fintype Place]

/-- Soundness is decidable: find a closed level of the markings reachable from `{i}`, or a pumping
pair, which makes the net unbounded and hence unsound. At a closed level, check the finitely many
markings of the level, deciding the reachability of the final marking from each with
`decidableReachable`. -/
instance decidableSound (i o : Place) : Decidable (N.Sound i o) :=
  have at_level : ∀ n, N.Closed (token i) n ∨ N.PumpWithin (token i) n →
      Decidable (N.Sound i o) :=
    fun n hn =>
      if hc : N.Closed (token i) n then
        have hb := bounded_of_closed N hc
        have : Decidable (∀ M ∈ N.reachSet (token i) n, M ⇝[N] token o) :=
          @Finset.decidableDforallFinset _ (N.reachSet (token i) n) (fun M _ => M ⇝[N] token o)
            fun M hM => decidableReachable M (token o)
              (hb.of_reachable (reachable_of_mem_reachSet N hM))
        decidable_of_iff _ (sound_iff_checks hc).symm
      else
        isFalse fun hs => not_bounded_of_pumpWithin N (hn.resolve_left hc) hs.bounded_net
  at_level _ (searchNat_spec (fun n => N.Closed (token i) n ∨ N.PumpWithin (token i) n)
    (exists_level N (token i)))

end PetriNet

end Cslib
