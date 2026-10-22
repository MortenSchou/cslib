<pre>
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
</pre>

# Rationally definable sets and Fourier–Motzkin elimination

A set `C ⊆ ℚ^κ` is `RatDefinable` if it is a finite union of finite systems of homogeneous linear
constraints `∑ i, a i * x i ≥ 0` (or `> 0`) with integer coefficients. This is the disjunctive
normal form of quantifier-free formulas in the first-order theory of `(ℚ; +, ≤, 0)`.

- [Basic](Basic.lean): `StrictRel`, `LinCons`, `RatDefinable`, and closure under `∪`, `∩`, `∅`,
  `univ`, finite unions (`iUnion_list`), integer linear preimages (`preimage`) and reindexing of
  coordinates (`comap`), finite intersections of definable families (`forall_fintype`), and the
  sets cut out by one linear form or coordinate (`zero`, `coord_nonneg`, `coord_pos`).
- [FourierMotzkin](FourierMotzkin.lean): one step of Fourier–Motzkin elimination of a coordinate
  `a` on explicit lists of constraints (`elimSystem`, with correctness theorem
  `exists_holds_iff_elimSystem`), and the closure of `RatDefinable` under projection
  (`RatDefinable.proj_one`, `RatDefinable.proj_finset`, `RatDefinable.proj`), i.e. quantifier
  elimination for `(ℚ; +, ≤)`.

`elimSystem` is a computable function on `List (LinCons κ)`, so it can serve as the basis of an
effective decision procedure; only its correctness is proved here.

Mathlib has no counterpart: `Mathlib.Tactic.Linarith.Oracle.FourierMotzkin` is a certificate-search
oracle without a semantic correctness theorem, `Mathlib.Geometry.Convex.Cone` has no
Minkowski–Weyl or projection results, and the Presburger/semilinear files treat `ℕ`.
