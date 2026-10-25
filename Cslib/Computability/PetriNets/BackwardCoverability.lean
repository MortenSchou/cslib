/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Coverability
public import Cslib.Computability.PetriNets.WSTS
public import Cslib.Computability.WSTS.Coverability

/-! # Backward coverability

To decide whether a target marking `M` is coverable from `M₀`, work backwards from the
upward-closed set of markings above `M`. Let `Pre U` be the markings that can fire one transition
into `U`. Monotonicity of firing makes `Pre U` upward closed whenever `U` is. Starting from the
markings above `M` and repeatedly adding `Pre`, the union of the resulting ascending chain is the
set of markings from which `M` is coverable. Over finitely many places, Dickson's lemma makes the
chain stabilise after finitely many steps.

All of this is the generic backward coverability of `Cslib.WSTS` for the marking graph; the
definitions and lemmas here are specialisations of it, stated with the net as an explicit argument.
Only the soundness half is needed without `Finite Place`, since firing is strongly monotone for
every net (`PetriNet.instStronglyMonotone`).

## Main definitions

- `PetriNet.predSet`: the one-step predecessors of a set of markings.
- `PetriNet.backStep`: keep a set and add its predecessors.
- `PetriNet.backSeq`: the backward iteration from the markings above a target.

## Main statements

- `PetriNet.coverable_iff_exists_mem_backSeq`: coverability is the union of the iteration.
- `PetriNet.exists_backSeq_fixpoint`: over finitely many places, the iteration reaches a fixpoint
  that equals the set of markings from which the target is coverable. It is the generic
  `Cslib.WSTS.exists_backSeq_fixpoint`.

## References

* [P. A. Abdulla, K. Cerans, B. Jonsson, Y.-K. Tsay, *Algorithmic Analysis of Programs with Well
  Quasi-Ordered Domains*][Abdulla2000]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*} (N : PetriNet Place Transition)

/-- The markings from which a single firing leads into `U`. -/
abbrev predSet (U : Set (Marking Place)) : Set (Marking Place) :=
  WSTS.predSet N.lts U

/-- One backward step: keep `U` and add its predecessors. -/
abbrev backStep (U : Set (Marking Place)) : Set (Marking Place) :=
  WSTS.backStep N.lts U

/-- The backward iteration starting from the markings above the target `M`. -/
abbrev backSeq (M : Marking Place) (n : ℕ) : Set (Marking Place) :=
  WSTS.backSeq N.lts M n

variable {N}

theorem predSet_isUpperSet {U : Set (Marking Place)} (hU : IsUpperSet U) :
    IsUpperSet (N.predSet U) :=
  WSTS.predSet_isUpperSet hU

theorem backStep_isUpperSet {U : Set (Marking Place)} (hU : IsUpperSet U) :
    IsUpperSet (N.backStep U) :=
  WSTS.backStep_isUpperSet hU

theorem isUpperSet_backSeq (M : Marking Place) (n : ℕ) : IsUpperSet (N.backSeq M n) :=
  WSTS.isUpperSet_backSeq M n

theorem backSeq_succ (M : Marking Place) (n : ℕ) :
    N.backSeq M (n + 1) = N.backStep (N.backSeq M n) :=
  WSTS.backSeq_succ M n

theorem backSeq_mono (M : Marking Place) : Monotone (N.backSeq M) :=
  WSTS.backSeq_mono M

/-- Everything in the backward iteration can cover the target. -/
theorem coverable_of_mem_backSeq {M M₀ : Marking Place} {n : ℕ} (h : M₀ ∈ N.backSeq M n) :
    N.Coverable M₀ M :=
  WSTS.coverable_of_mem_backSeq h

/-- Every coverable marking appears in the backward iteration after as many steps as the
shortest covering firing sequence has transitions. -/
theorem mem_backSeq_of_mTr {M M₀ M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M₀ ts M') (hle : M ≤ M') : M₀ ∈ N.backSeq M ts.length :=
  WSTS.mem_backSeq_of_mTr h hle

/-- Coverability is the union of the backward iteration. -/
theorem coverable_iff_exists_mem_backSeq {M M₀ : Marking Place} :
    N.Coverable M₀ M ↔ ∃ n, M₀ ∈ N.backSeq M n :=
  WSTS.coverable_iff_exists_mem_backSeq

/-- Over finitely many places, the backward iteration reaches a fixpoint, and that fixpoint is
exactly the set of markings from which the target is coverable. -/
theorem exists_backSeq_fixpoint [Finite Place] (M : Marking Place) :
    ∃ n, N.backStep (N.backSeq M n) = N.backSeq M n ∧
      ∀ M₀, N.Coverable M₀ M ↔ M₀ ∈ N.backSeq M n :=
  WSTS.exists_backSeq_fixpoint (lts := N.lts) M

end PetriNet

end Cslib
