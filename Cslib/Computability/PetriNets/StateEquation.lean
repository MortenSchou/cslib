/-
Copyright (c) 2026 Morten Schou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Morten Schou
-/

module

public import Cslib.Computability.PetriNets.Semantics
public import Mathlib.Algebra.BigOperators.Group.List.Basic
public import Mathlib.Tactic.Abel

/-! # The state equation

Firing a transition `t` changes a marking by the integer vector `post t - pre t`, its
*incidence*. Hence the marking reached by a firing sequence is the initial marking plus the sum of
the incidences of the fired transitions. This gives a necessary (but not sufficient) condition for
reachability.

## Main definitions

- `PetriNet.Marking.toInt`: view a marking as an integer vector.
- `PetriNet.incidence`: the effect `post t - pre t` of a transition.
- `PetriNet.effect`: the total effect of a firing sequence.

## Main statements

- `PetriNet.mTr_toInt`: the state equation for firing sequences.
- `PetriNet.Reachable.exists_toInt_eq`: the state equation for reachable markings.
- `PetriNet.mTr_eq_iff_effect_eq_zero`: a firing sequence returns to its start iff its effect is
  zero.
- `PetriNet.mTr_replicate`: a cyclic firing sequence can be repeated.

## References

* [T. Murata, *Petri nets: Properties, analysis and applications*][Murata1989]
-/

@[expose] public section

namespace Cslib

namespace PetriNet

variable {Place : Type*} {Transition : Type*}

/-- View a marking as an integer vector. -/
noncomputable def Marking.toInt : Marking Place →+ (Place →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom (Nat.castAddMonoidHom ℤ)

variable (N : PetriNet Place Transition)

/-- The effect of firing `t`: tokens produced minus tokens consumed. -/
noncomputable def incidence (t : Transition) : Place →₀ ℤ :=
  Marking.toInt (t •[N]) - Marking.toInt (•[N] t)

/-- The total effect of a firing sequence. -/
noncomputable def effect (ts : List Transition) : Place →₀ ℤ :=
  (ts.map N.incidence).sum

variable {N}

@[simp] theorem effect_nil : N.effect [] = 0 := rfl

@[simp] theorem effect_cons (t : Transition) (ts : List Transition) :
    N.effect (t :: ts) = N.incidence t + N.effect ts := by
  simp [effect]

theorem effect_append (ts₁ ts₂ : List Transition) :
    N.effect (ts₁ ++ ts₂) = N.effect ts₁ + N.effect ts₂ := by
  simp [effect]

theorem Fires.toInt {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    Marking.toInt M' = Marking.toInt M + N.incidence t := by
  obtain ⟨R, rfl, rfl⟩ := h
  simp only [incidence, map_add]
  abel

/-- The state equation: a firing sequence changes the marking by its total effect. -/
theorem mTr_toInt {M M' : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M') :
    Marking.toInt M' = Marking.toInt M + N.effect ts := by
  induction h with
  | refl => simp
  | stepL htr _ ih => rw [ih, htr.toInt, effect_cons]; abel

/-- Every reachable marking satisfies the state equation for some firing sequence. -/
theorem Reachable.exists_toInt_eq {M M' : Marking Place} (h : M ⇝[N] M') :
    ∃ ts, Marking.toInt M' = Marking.toInt M + N.effect ts :=
  let ⟨ts, hts⟩ := h
  ⟨ts, mTr_toInt hts⟩

theorem Marking.toInt_injective : Function.Injective (Marking.toInt (Place := Place)) :=
  fun _ _ h => Finsupp.mapRange_injective (Nat.cast : ℕ → ℤ) (by simp) Nat.cast_injective h

/-- A firing sequence returns to its starting marking exactly when its total effect is zero.
Such a sequence is called a *T-invariant*. -/
theorem mTr_eq_iff_effect_eq_zero {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : M' = M ↔ N.effect ts = 0 := by
  have heq := mTr_toInt h
  constructor
  · rintro rfl
    simpa using heq
  · intro h0
    exact Marking.toInt_injective (by rw [heq, h0, add_zero])

/-- A cyclic firing sequence can be repeated any number of times. -/
theorem mTr_replicate {M : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M) (n : ℕ) :
    N.lts.MTr M (List.replicate n ts).flatten M := by
  induction n with
  | zero => exact .refl
  | succ n ih =>
    rw [List.replicate_succ, List.flatten_cons]
    exact LTS.MTr.comp _ h ih

end PetriNet

end Cslib
