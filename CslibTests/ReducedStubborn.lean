/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.PetriNets.Decision.ReducedStubborn

/-! # Deadlocks through a reduction and stubborn sets

Nets with several independent chains of series transitions. The structural reduction
(`PetriNet.reduce`) fuses each chain into one transition, which removes the positions inside
the chains, and the stubborn sets (`PetriNet.stubbornFinset`) then avoid the interleavings of
the independent transitions that remain.

* `chains k len` has `k` independent chains of `len` transitions, each with a token at its start.
  The marking with all tokens at the ends of the chains is a reachable deadlock.
* `looped k len` has the same chains and a transition `done` that takes the tokens from the ends of
  all chains and puts them back. It is deadlock-free.

For `k` chains of length `len`, the net has `(len + 1) ^ k` reachable markings, the reduced net
`2 ^ k`, and the stubborn-reduced graph of the reduced net `k + 1`. For `k = 4` and `len = 3`
these are 256, 16 and 5 (computed with `#eval`; the kernel needs over a minute for the full net, so
the tests use `k = 3`: 64, 8 and 4).

The decision procedures with an explicit closed level (`decideDeadlockStubborn`) only evaluate the
reduced net and its stubborn-reduced graph. Those that search for the level need the boundedness of
the net, which is shown here by exploring the full net, so they are only run on the small nets.
-/

namespace CslibTests.ReducedStubborn

open Cslib PetriNet
open scoped PetriNet

/-! ### Independent chains

The place `j` of the chain `c` is `c * (len + 1) + j`, and the transition `j` of the chain `c` is
`c * len + j`. -/

/-- `k` independent chains, each of `len` series transitions. -/
def chains (k len : ℕ) [NeZero (k * (len + 1))] :
    PetriNet (Fin (k * (len + 1))) (Fin (k * len)) where
  pre t := {Fin.ofNat _ (t.val / len * (len + 1) + t.val % len)}
  post t := {Fin.ofNat _ (t.val / len * (len + 1) + t.val % len + 1)}

/-- A token at the start of each chain. -/
def chains₀ (k len : ℕ) [NeZero (k * (len + 1))] : Marking (Fin (k * (len + 1))) :=
  ((List.range k).map fun c => Fin.ofNat (k * (len + 1)) (c * (len + 1)) : List _)

/-- Three chains of three transitions: 12 places, 9 transitions. -/
abbrev C : PetriNet (Fin 12) (Fin 9) := chains 3 3

abbrev C₀ : Marking (Fin 12) := chains₀ 3 3

/-- The net has `4 ^ 3 = 64` reachable markings. -/
example : (C.reachSet C₀ 9).card = 64 := by decide +kernel

/-- The search fuses each chain into one transition, leaving 6 places and 3 transitions. The
reduced net has `2 ^ 3 = 8` reachable markings, and the stubborn-reduced graph of the reduced net
only 4. -/
example : (reduce C C₀).places = 6 ∧ (reduce C C₀).transitions = 3 ∧
    ((reduce C C₀).net.reachSet (reduce C C₀).init 3).card = 8 ∧
    ((reduce C C₀).net.reducedReachSet (reduce C C₀).net.stubbornFinset
      (reduce C C₀).init 3).card = 4 := by decide +kernel

/-- Its level 3 is closed. -/
theorem C_closed : (reduce C C₀).net.ReducedClosed (reduce C C₀).net.stubbornFinset
    (reduce C C₀).init 3 := by decide +kernel

/-- A dead marking is reachable, decided on the stubborn-reduced graph of the reduced net. -/
example : ∃ M, C₀ ⇝[C] M ∧ C.Dead M :=
  of_decide_eq_true (inst := decideDeadlockStubborn C C₀ C_closed) (by decide +kernel)

/-- The net is not deadlock-free. -/
example : ¬ ∀ M, C₀ ⇝[C] M → ¬ C.Dead M :=
  of_decide_eq_false (inst := decideDeadlockFreeStubborn C C₀ C_closed) (by decide +kernel)

/-- The composition of the two reductions, for the certificate found by the search. -/
example : (∃ M, C₀ ⇝[C] M ∧ C.Dead M) ↔
    (reduce C C₀).net.StubbornDeadlockWithin (reduce C C₀).init 3 :=
  (reduce C C₀).reduces.exists_dead_iff_stubbornDeadlockWithin C_closed

/-! ### A larger net, where only the reductions can decide

Five chains of four transitions have `5 ^ 5 = 3125` reachable markings, which the kernel does not
enumerate in reasonable time. The reduced net has 32, and the stubborn-reduced graph 6. -/

abbrev B : PetriNet (Fin 25) (Fin 20) := chains 5 4

abbrev B₀ : Marking (Fin 25) := chains₀ 5 4

example : (reduce B B₀).places = 10 ∧ (reduce B B₀).transitions = 5 ∧
    ((reduce B B₀).net.reachSet (reduce B B₀).init 5).card = 32 ∧
    ((reduce B B₀).net.reducedReachSet (reduce B B₀).net.stubbornFinset
      (reduce B B₀).init 5).card = 6 := by decide +kernel

theorem B_closed : (reduce B B₀).net.ReducedClosed (reduce B B₀).net.stubbornFinset
    (reduce B B₀).init 5 := by decide +kernel

example : ∃ M, B₀ ⇝[B] M ∧ B.Dead M :=
  of_decide_eq_true (inst := decideDeadlockStubborn B B₀ B_closed) (by decide +kernel)

/-! ### Independent chains with a final loop

A transition `done`, the last, takes the tokens from the ends of all chains and puts them back. It
is enabled only when every chain has finished, and then forever, so the net is deadlock-free. -/

/-- `k` chains of `len` transitions and the transition `done`. -/
def looped (k len : ℕ) [NeZero (k * (len + 1))] :
    PetriNet (Fin (k * (len + 1))) (Fin (k * len + 1)) where
  pre t :=
    if t.val = k * len then
      ((List.range k).map fun c => Fin.ofNat (k * (len + 1)) (c * (len + 1) + len) : List _)
    else {Fin.ofNat _ (t.val / len * (len + 1) + t.val % len)}
  post t :=
    if t.val = k * len then
      ((List.range k).map fun c => Fin.ofNat (k * (len + 1)) (c * (len + 1) + len) : List _)
    else {Fin.ofNat _ (t.val / len * (len + 1) + t.val % len + 1)}

/-- Three chains of three transitions and `done`: 12 places, 10 transitions. -/
abbrev Y : PetriNet (Fin 12) (Fin 10) := looped 3 3

abbrev Y₀ : Marking (Fin 12) := chains₀ 3 3

/-- The net has 64 reachable markings. -/
example : (Y.reachSet Y₀ 10).card = 64 := by decide +kernel

theorem Y_bounded : Y.Bounded Y₀ :=
  bounded_of_closed Y (n := 10) (by decide +kernel)

/-- The chains are fused, and the transition `done` remains: 6 places and 4 transitions. The reduced
net has 8 reachable markings, and the stubborn-reduced graph 4. -/
example : (reduce Y Y₀).places = 6 ∧ (reduce Y Y₀).transitions = 4 ∧
    ((reduce Y Y₀).net.reachSet (reduce Y Y₀).init 4).card = 8 ∧
    ((reduce Y Y₀).net.reducedReachSet (reduce Y Y₀).net.stubbornFinset
      (reduce Y Y₀).init 4).card = 4 := by decide +kernel

theorem Y_closed : (reduce Y Y₀).net.ReducedClosed (reduce Y Y₀).net.stubbornFinset
    (reduce Y Y₀).init 4 := by decide +kernel

/-- The net is deadlock-free, decided on the stubborn-reduced graph of the reduced net. -/
example : ∀ M, Y₀ ⇝[Y] M → ¬ Y.Dead M :=
  of_decide_eq_true (inst := decideDeadlockFreeStubborn Y Y₀ Y_closed) (by decide +kernel)

/-- The same, with the closed level found by search, given that the net is bounded. -/
example : ∀ M, Y₀ ⇝[Y] M → ¬ Y.Dead M :=
  of_decide_eq_true (inst := decideDeadlockFreeReducedStubborn Y Y₀ Y_bounded)
    (by decide +kernel)

end CslibTests.ReducedStubborn
