/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.VAS.EffectiveSearch
public import Cslib.Computability.VAS.Separators

/-! # Non-reachability of vector addition systems is recursively enumerable

This file combines the two halves of the development.

* `Cslib.VAS.not_reach_iff` (`Separators`) is Leroux's theorem: a configuration is not reachable
  iff a Presburger (semilinear) forward inductive invariant contains the source and not the target.
* `Cslib.rePred_exists_certificate` (`EffectiveSearch`) is a semi-algorithm: the invariants are
  coded and checked by the decision procedure for Presburger arithmetic, so the existence of a
  certificate is recursively enumerable.

The two files are kept apart so that the coding and the search do not depend on the combinatorics
of Leroux's theorem.

## Main statements

- `Cslib.ReachInput.not_reaches_iff_exists_certificate`: non-reachability of a coded VAS is the
  existence of a coded certificate.
- `Cslib.VAS.not_reaches_rePred`: non-reachability of coded VAS is recursively enumerable.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

/-- Non-reachability of a coded VAS is the existence of a coded certificate. -/
theorem ReachInput.not_reaches_iff_exists_certificate (p : ReachInput) :
    ¬ p.Reaches ↔ ∃ r : SLCode, p.1.Certificate p.2.1 p.2.2 r := by
  rw [ReachInput.Reaches, VAS.not_reach_iff]
  constructor
  · rintro ⟨X, hX, hind, hx, hy⟩
    obtain ⟨r, rfl⟩ := isSemilinearSet_iff_exists_code.1 hX
    exact ⟨r, hind, hx, hy⟩
  · rintro ⟨r, hind, hx, hy⟩
    exact ⟨r.set p.1.1, isSemilinearSet_iff_exists_code.2 ⟨r, rfl⟩, hind, hx, hy⟩

/-- **The semi-algorithm**: non-reachability of coded VAS is recursively enumerable. -/
theorem VAS.not_reaches_rePred : REPred fun p : ReachInput => ¬ p.Reaches :=
  rePred_exists_certificate.of_eq fun p => p.not_reaches_iff_exists_certificate.symm

end Cslib
