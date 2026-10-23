/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Mathlib.Data.Finsupp.Multiset

/-! # Executable Petri nets

`PetriNet` uses `Finsupp` markings, which are noncomputable. This file gives a computable
presentation using `Multiset`, together with a translation to `PetriNet` and a proof that the two
firing rules agree. It is meant for examples and tests (`#eval`, `decide`).

## Main definitions

- `ExecPetriNet`: a net whose arc weights are multisets of places.
- `ExecPetriNet.toPetriNet`: the corresponding weighted net.
- `ExecPetriNet.enabled`, `ExecPetriNet.fire`, `ExecPetriNet.run`: computable semantics.

After `open scoped PetriNet`, a multiset of places is read as a marking wherever a marking is
expected, so `N.toPetriNet.Bounded M₀` is `N.toPetriNet.Bounded (Multiset.toFinsupp M₀)`.

A coercion from `ExecPetriNet` to `PetriNet` cannot be provided with any of Lean's coercion classes
(`Coe`, `CoeOut`, `CoeTail`, `CoeHead`, `CoeDep`, `CoeT`): Lean only inserts a coercion when the
target type is fully known, but the type of transitions of the target net is determined by the net
itself. Instead, the net slot of the notations `M [t⟩[N] M'` and `M ⇝[N] M'` is elaborated by
`net%`, which applies the instance of `PetriNet.ToPetriNet` for executable nets, and the module
`ExecutableForward` forwards the properties of nets to executable nets, so that `N.Bounded M₀` can
be written for `N.toPetriNet.Bounded M₀`.

## Main statements

- `ExecPetriNet.fires_iff`: the computable rule agrees with `PetriNet.Fires`.
-/

@[expose] public section

namespace Cslib

/-- A Petri net whose arc weights are multisets of places. -/
structure ExecPetriNet (Place Transition : Type*) where
  /-- Tokens consumed from each place when a transition fires. -/
  pre : Transition → Multiset Place
  /-- Tokens produced in each place when a transition fires. -/
  post : Transition → Multiset Place

namespace PetriNet

/-- Multisets of places are read as markings where a marking is expected. The coercion is scoped,
since it is only convenient in the context of Petri nets. -/
scoped instance {Place : Type*} [DecidableEq Place] : Coe (Multiset Place) (Marking Place) :=
  ⟨fun m => Multiset.toFinsupp m⟩

end PetriNet

namespace ExecPetriNet

open scoped PetriNet

variable {Place Transition : Type*}

/-- The weighted net with the same arcs. -/
def toPetriNet [DecidableEq Place] (N : ExecPetriNet Place Transition) :
    PetriNet Place Transition where
  pre t := Multiset.toFinsupp (N.pre t)
  post t := Multiset.toFinsupp (N.post t)

/-- Executable nets are read as weighted nets in the Petri net notation. -/
instance [DecidableEq Place] :
    PetriNet.ToPetriNet (ExecPetriNet Place Transition) Place Transition :=
  ⟨toPetriNet⟩

section Computable

variable (N : ExecPetriNet Place Transition)

/-- A transition is enabled if the marking contains its preset. -/
def enabled [DecidableEq Place] (M : Multiset Place) (t : Transition) : Bool :=
  decide (N.pre t ≤ M)

/-- Fire `t` at `M`, if enabled. -/
def fire [DecidableEq Place] (M : Multiset Place) (t : Transition) : Option (Multiset Place) :=
  if N.pre t ≤ M then some (M - N.pre t + N.post t) else none

/-- Run a firing sequence. -/
def run [DecidableEq Place] (M : Multiset Place) : List Transition → Option (Multiset Place)
  | [] => some M
  | t :: ts => (N.fire M t).bind fun M' => run M' ts

variable [DecidableEq Place] {N}

theorem toFinsupp_le_iff {a b : Multiset Place} :
    Multiset.toFinsupp a ≤ Multiset.toFinsupp b ↔ a ≤ b := by
  simp only [Finsupp.le_def, Multiset.le_iff_count, Multiset.toFinsupp_apply]

theorem toFinsupp_sub (a b : Multiset Place) :
    Multiset.toFinsupp (a - b) = Multiset.toFinsupp a - Multiset.toFinsupp b := by
  ext p
  simp [Multiset.toFinsupp_apply, Multiset.count_sub]

theorem enabled_toPetriNet_iff {M : Multiset Place} {t : Transition} :
    (Multiset.toFinsupp M) [t⟩[N] ↔ N.pre t ≤ M :=
  toFinsupp_le_iff

theorem fires_iff {M M' : Multiset Place} {t : Transition} :
    (Multiset.toFinsupp M) [t⟩[N] Multiset.toFinsupp M' ↔ N.fire M t = some M' := by
  unfold fire
  constructor
  · rintro ⟨R, h1, h2⟩
    have h1' : M = N.pre t + Multiset.toFinsupp.symm R := by
      apply Multiset.toFinsupp.injective
      simpa [toPetriNet] using h1
    have h2' : M' = Multiset.toFinsupp.symm R + N.post t := by
      apply Multiset.toFinsupp.injective
      simpa [toPetriNet] using h2
    subst h1' h2'
    simp
  · intro h
    split_ifs at h with hle
    obtain ⟨rfl⟩ := Option.some.inj h
    refine ⟨Multiset.toFinsupp (M - N.pre t), ?_, ?_⟩
    · rw [toPetriNet, ← map_add, add_tsub_cancel_of_le hle]
    · simp [toPetriNet, map_add]

theorem fires_toFinsupp_iff_exists {M M' : Multiset Place} {t : Transition} :
    (Multiset.toFinsupp M) [t⟩[N] Multiset.toFinsupp M' ↔
      ∃ R, M = N.pre t + R ∧ M' = R + N.post t := by
  constructor
  · rintro ⟨R, h1, h2⟩
    obtain ⟨R', rfl⟩ := Multiset.toFinsupp.surjective R
    exact ⟨R', Multiset.toFinsupp.injective (by simpa [toPetriNet] using h1),
      Multiset.toFinsupp.injective (by simpa [toPetriNet] using h2)⟩
  · rintro ⟨R, rfl, rfl⟩
    exact ⟨Multiset.toFinsupp R, by simp [toPetriNet], by simp [toPetriNet]⟩

section Run

open PetriNet

variable (N)

theorem run_append (M : Multiset Place) (ts₁ ts₂ : List Transition) :
    N.run M (ts₁ ++ ts₂) = (N.run M ts₁).bind fun M' => N.run M' ts₂ := by
  induction ts₁ generalizing M with
  | nil => simp [run]
  | cons t ts ih =>
    simp only [List.cons_append, run]
    cases N.fire M t <;> simp [ih]

theorem fires_toFinsupp_iff {M : Multiset Place} {t : Transition} {M' : Marking Place} :
    (Multiset.toFinsupp M) [t⟩[N] M' ↔
      ∃ m', M' = Multiset.toFinsupp m' ∧ N.fire M t = some m' := by
  constructor
  · intro h
    obtain ⟨m', rfl⟩ := Multiset.toFinsupp.surjective M'
    exact ⟨m', rfl, fires_iff.1 h⟩
  · rintro ⟨m', rfl, h⟩
    exact fires_iff.2 h

theorem run_eq_some_iff {ts : List Transition} {M M' : Multiset Place} :
    N.run M ts = some M' ↔
      N.toPetriNet.lts.MTr (Multiset.toFinsupp M) ts (Multiset.toFinsupp M') := by
  induction ts generalizing M with
  | nil =>
    simp only [run, Option.some.injEq, LTS.MTr.nil_iff]
    exact ⟨fun h => h ▸ rfl, fun h => Multiset.toFinsupp.injective h⟩
  | cons t ts ih =>
    constructor
    · intro h
      simp only [run, Option.bind_eq_some_iff] at h
      obtain ⟨m'', hf, hrest⟩ := h
      exact .stepL (fires_iff.2 hf) (ih.1 hrest)
    · intro h
      cases h with
      | stepL htr hrest =>
        obtain ⟨m'', rfl, hf⟩ := (fires_toFinsupp_iff N).1 htr
        simp only [run, hf, Option.bind_some]
        exact ih.2 hrest

end Run

end Computable

end ExecPetriNet

end Cslib
