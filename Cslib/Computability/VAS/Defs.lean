/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Init
public import Cslib.Foundations.Semantics.LTS.Relation
public import Mathlib.Logic.Relation
public import Mathlib.ModelTheory.Arithmetic.Presburger.Semilinear.Defs

/-! # Vector addition systems: definitions

The definitions for the formalisation of the decidability of the reachability problem of vector
addition systems (VAS) by Presburger inductive invariants (Leroux). This file fixes the shared
vocabulary; the basic lemmas are in `Cslib.Computability.VAS.Basic`.

## Main definitions

- `VAS.Config`: a configuration, a vector of natural numbers.
- `VAS`: a finite set of actions in `ℤ^ι`.
- `VAS.Step`, `VAS.Move`, `VAS.Reach`: the step, one-step and reachability relations.
- `VAS.lts`: the labelled transition system of a VAS, whose labels are the actions; `VAS.Reach`
  is reachability in it (`VAS.reach_iff_canReach`).
- `VAS.post`, `VAS.pre`: the forward and backward reachable sets.
- `VAS.IsInductive`, `VAS.IsBackInductive`: forward and backward inductive invariants.
- `VAS.Separator`, `VAS.domain`: pairs of semilinear sets with no run from the first to the second.

## References

* [J. Leroux, *Vector Addition Systems Reachability Problem (A Simpler Solution)*][Leroux2012]
-/

@[expose] public section

namespace Cslib

/-- A configuration of a `ι`-dimensional VAS: a vector of natural numbers. -/
abbrev VASConfig (ι : Type*) := ι → ℕ

variable {ι : Type*}

/-- The integer view of a configuration. -/
def VASConfig.toInt (c : VASConfig ι) : ι → ℤ := fun i => (c i : ℤ)

/-- A vector addition system: a finite set of actions in `ℤ^ι`. -/
structure VAS (ι : Type*) where
  /-- The finite set of actions. -/
  acts : Finset (ι → ℤ)

namespace VAS

variable (V : VAS ι)

/-- `c --a--> c'`: the action `a` is applied and the result stays in `ℕ^ι`. -/
def Step (c : VASConfig ι) (a : ι → ℤ) (c' : VASConfig ι) : Prop :=
  a ∈ V.acts ∧ c'.toInt = c.toInt + a

/-- One-step move, forgetting the action. -/
def Move (c c' : VASConfig ι) : Prop := ∃ a, V.Step c a c'

/-- The labelled transition system of the VAS: its states are the configurations and its labels
are the actions. -/
def lts : LTS (VASConfig ι) (ι → ℤ) := ⟨V.Step⟩

/-- A move is a step of the labelled transition system, forgetting the action. -/
theorem move_eq_unlabelledTr : V.Move = V.lts.UnlabelledTr := rfl

/-- The reachability relation of the VAS: reachability in its labelled transition system. -/
abbrev Reach : VASConfig ι → VASConfig ι → Prop := V.lts.CanReach

variable {V} in
/-- Reachability is reflexive. -/
@[refl]
theorem Reach.refl {c : VASConfig ι} : V.Reach c c := LTS.CanReach.refl V.lts c

variable {V} in
/-- A move gives reachability. -/
theorem Reach.single {c c' : VASConfig ι} (h : V.Move c c') : V.Reach c c' :=
  LTS.CanReach.of_unlabelledTr h

/-- Reachability is the reflexive-transitive closure of moves. -/
theorem reach_iff_reflTransGen {c c' : VASConfig ι} :
    V.Reach c c' ↔ Relation.ReflTransGen V.Move c c' :=
  (LTS.reflTransGen_unlabelledTr_iff V.lts).symm

/-- The configurations forward reachable from `X`. -/
def post (X : Set (VASConfig ι)) : Set (VASConfig ι) := {c' | ∃ c ∈ X, V.Reach c c'}

/-- The configurations backward reachable from `Y`. -/
def pre (Y : Set (VASConfig ι)) : Set (VASConfig ι) := {c | ∃ c' ∈ Y, V.Reach c c'}

/-- A forward inductive invariant: a set closed under moves. -/
def IsInductive (X : Set (VASConfig ι)) : Prop := ∀ c ∈ X, ∀ c', V.Move c c' → c' ∈ X

/-- A backward inductive invariant. -/
def IsBackInductive (Y : Set (VASConfig ι)) : Prop := ∀ c' ∈ Y, ∀ c, V.Move c c' → c ∈ Y

/-- A (Presburger) separator: a pair of semilinear sets of configurations with no run from the
first to the second. -/
structure Separator (X Y : Set (VASConfig ι)) : Prop where
  /-- The first set is semilinear. -/
  semilinear_left : IsSemilinearSet X
  /-- The second set is semilinear. -/
  semilinear_right : IsSemilinearSet Y
  /-- There is no run from the first set to the second. -/
  no_run : ∀ x ∈ X, ∀ y ∈ Y, ¬ V.Reach x y

/-- The domain `ℕ^ι \ (X ∪ Y)` of a separator. -/
def domain (X Y : Set (VASConfig ι)) : Set (VASConfig ι) := (X ∪ Y)ᶜ

end VAS

end Cslib
