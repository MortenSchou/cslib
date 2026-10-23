/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.ExecutableBoundedness
public import Cslib.Computability.PetriNets.ExecutableReachability
public import Cslib.Computability.PetriNets.Soundness

/-! # Checking soundness of executable workflow nets

Soundness of a net with source `i` and sink `o` is decidable for executable nets. A sound net is
bounded, so a pumping pair from `{i}` shows unsoundness. Otherwise a closed level `n` of the
markings reachable from `{i}` contains all reachable markings, and soundness reduces to three checks
on that level: markings with a token in the sink are the final marking, every transition is enabled
somewhere, and the final marking is reachable from every marking of the level. The last check uses
`ExecPetriNet.decidableReachable`.

## Main definitions

- `ExecPetriNet.decidableSound`: the decision procedure for soundness.

## Main statements

- `ExecPetriNet.sound_iff_checks`: soundness at a closed level is the three finite checks.
-/

@[expose] public section

namespace Cslib

namespace ExecPetriNet

open PetriNet

variable {Place Transition : Type*} [DecidableEq Place] [Fintype Transition]
  (N : ExecPetriNet Place Transition)

variable {N}

/-- The single token as a multiset marking. -/
theorem token_eq_toFinsupp (p : Place) :
    PetriNet.token p = Multiset.toFinsupp ({p} : Multiset Place) := by
  simp [PetriNet.token, Multiset.toFinsupp_singleton]

omit [Fintype Transition] in
/-- Soundness, stated for markings given by multisets. -/
theorem sound_iff_toFinsupp {i o : Place} :
    N.toPetriNet.Sound i o ↔
      (∀ M, Multiset.toFinsupp {i} ⇝[N] M →
        M ⇝[N] Multiset.toFinsupp {o}) ∧
      (∀ M, Multiset.toFinsupp {i} ⇝[N] M →
        Multiset.toFinsupp {o} ≤ M → M = Multiset.toFinsupp {o}) ∧
      ∀ t, ∃ M, Multiset.toFinsupp {i} ⇝[N] M ∧ M [t⟩[N] := by
  simp only [← token_eq_toFinsupp]
  exact ⟨fun h => ⟨h.completion, h.proper, h.noDead⟩, fun ⟨a, b, c⟩ => ⟨a, b, c⟩⟩

/-- On a closed level of the markings reachable from `{i}`, soundness is a finite check, apart from
the reachability of the final marking from each marking of the level. -/
theorem sound_iff_checks {i o : Place} {n : ℕ} (hc : N.Closed {i} n) :
    N.toPetriNet.Sound i o ↔ (∀ M ∈ N.reachSet {i} n, {o} ≤ M → M = {o}) ∧
      (∀ t, ∃ M ∈ N.reachSet {i} n, N.pre t ≤ M) ∧
      ∀ M ∈ N.reachSet {i} n,
        M ⇝[N] Multiset.toFinsupp {o} := by
  rw [sound_iff_toFinsupp]
  constructor
  · rintro ⟨hcomp, hp, hd⟩
    refine ⟨fun M hM hle => ?_, fun t => ?_, fun M hM => hcomp _ (reachable_of_mem_reachSet N hM)⟩
    · exact Multiset.toFinsupp.injective
        (hp _ (reachable_of_mem_reachSet N hM) (toFinsupp_le_iff.2 hle))
    · obtain ⟨X, hX, hen⟩ := hd t
      obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective X
      exact ⟨M, mem_reachSet_of_reachable N hc hX, enabled_toPetriNet_iff.1 hen⟩
  · rintro ⟨hp, hd, hcomp⟩
    refine ⟨fun X hX => ?_, fun X hX hle => ?_, fun t => ?_⟩
    · obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective X
      exact hcomp M (mem_reachSet_of_reachable N hc hX)
    · obtain ⟨M, rfl⟩ := Multiset.toFinsupp.surjective X
      rw [hp M (mem_reachSet_of_reachable N hc hX) (toFinsupp_le_iff.1 hle)]
    · obtain ⟨M, hM, hle⟩ := hd t
      exact ⟨Multiset.toFinsupp M, reachable_of_mem_reachSet N hM, enabled_toPetriNet_iff.2 hle⟩

variable [Fintype Place]

/-- Soundness of an executable net is decidable: find a closed level of the markings reachable from
`{i}`, or a pumping pair, which makes the net unbounded and hence unsound. At a closed level, check
the finitely many markings of the level, deciding the reachability of the final marking from each
with `decidableReachable`. -/
instance decidableSound (i o : Place) : Decidable (N.toPetriNet.Sound i o) :=
  have at_level : ∀ n, N.Closed {i} n ∨ N.PumpWithin {i} n → Decidable (N.toPetriNet.Sound i o) :=
    fun n hn =>
      if hc : N.Closed {i} n then
        have hb := bounded_of_closed N hc
        have hC : Decidable (∀ M ∈ N.reachSet {i} n,
            M ⇝[N] Multiset.toFinsupp {o}) :=
          have inst : ∀ M (hM : M ∈ N.reachSet {i} n),
              Decidable (M ⇝[N] Multiset.toFinsupp {o}) :=
            fun M hM => decidableReachable M {o} (hb.of_reachable (reachable_of_mem_reachSet N hM))
          @Finset.decidableDforallFinset _ (N.reachSet {i} n)
            (fun M _ => M ⇝[N] Multiset.toFinsupp {o}) inst
        decidable_of_iff ((∀ M ∈ N.reachSet {i} n, {o} ≤ M → M = {o}) ∧
          (∀ t, ∃ M ∈ N.reachSet {i} n, N.pre t ≤ M) ∧
          ∀ M ∈ N.reachSet {i} n,
            M ⇝[N] Multiset.toFinsupp {o})
          (sound_iff_checks hc).symm
      else
        isFalse fun hs => by
          have hp := hn.resolve_left hc
          have := hs.bounded_net
          rw [token_eq_toFinsupp] at this
          exact not_bounded_of_pumpWithin N hp this
  at_level _ (searchNat_spec (fun n => N.Closed {i} n ∨ N.PumpWithin {i} n) (exists_level N {i}))

end ExecPetriNet

end Cslib
