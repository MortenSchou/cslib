/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

import Cslib.Computability.VAS.Decidable

/-! # Tests for the effective layer of the VAS decidability proof

Small certificates checked by evaluating the Presburger decision procedure in the kernel. -/

namespace CslibTests.VASEffective

open Cslib Cslib.Presburger

/-- The VAS of dimension one with the single action `-1`. -/
def dec : VASCode := (1, [[-1]])

/-- The set `{0, 1, 2}`. -/
def upTo2 : SLCode := [([0], []), ([1], []), ([2], [])]

/-- The set of even numbers, as a linear set. -/
def evens : SLCode := [([0], [[2]])]

/-- `{0, 1, 2}` is an inductive set of `dec` containing `2` but not `3`. -/
example : (PForm.certForm dec [2] [3] upTo2).valid = true := by decide +kernel

/-- `1` belongs to the set, so it is not a certificate for the target `1`. -/
example : (PForm.certForm dec [2] [1] upTo2).valid = false := by decide +kernel

/-- The VAS with the single action `+2` preserves the even numbers. -/
example : (PForm.certForm (1, [[2]]) [0] [1] evens).valid = true := by decide +kernel

/-- The action `+1` does not preserve the even numbers. -/
example : (PForm.certForm (1, [[1]]) [0] [1] evens).valid = false := by decide +kernel

/-- The kernel-checked certificate proves that `3` is not reachable from `2` in `dec`. -/
example : ¬ ReachInput.Reaches (dec, [2], [3]) :=
  (ReachInput.not_reaches_iff_exists_certificate _).2
    ⟨upTo2, (PForm.valid_certForm_iff _ _ _ _).1 (by decide +kernel)⟩

end CslibTests.VASEffective
