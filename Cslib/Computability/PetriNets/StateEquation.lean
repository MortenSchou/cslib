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

Firing a transition `t` at `M` leads to `M'` with `M' + pre t = M + post t`. Hence the marking `M'`
reached by a firing sequence `ts` satisfies `M' + Σ pre = M + Σ post`, the sums ranging over the
fired transitions. Viewing markings as integer vectors, this says that `M'` is `M` plus the sum
of the *incidences* `post t - pre t` of the fired transitions. This gives a necessary (but not
sufficient) condition for reachability.

The multiset form needs no decidable equality on places; the integer form does, to count tokens.

## Main definitions

- `PetriNet.Marking.toInt`: view a marking as an integer vector.
- `PetriNet.incidence`: the effect `post t - pre t` of a transition.
- `PetriNet.effect`: the total effect of a firing sequence.

## Main statements

- `PetriNet.mTr_add_sum_pre`: the state equation for firing sequences, on multisets.
- `PetriNet.mTr_toInt`: the state equation for firing sequences, on integer vectors.
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

variable {Place : Type*} {Transition : Type*} {N : PetriNet Place Transition}

/-- Firing `t` adds the postset and removes the preset. -/
theorem Fires.add_pre {M M' : Marking Place} {t : Transition} (h : M [t⟩[N] M') :
    M' + •[N] t = M + t •[N] := by
  obtain ⟨R, rfl, rfl⟩ := h
  abel

/-- The state equation on multisets: a firing sequence adds the postsets and removes the presets of
the fired transitions. -/
theorem mTr_add_sum_pre {M M' : Marking Place} {ts : List Transition} (h : N.lts.MTr M ts M') :
    M' + (ts.map N.pre).sum = M + (ts.map N.post).sum := by
  induction h with
  | refl => simp
  | @stepL M t M₁ ts M' htr _ ih =>
    rw [List.map_cons, List.map_cons, List.sum_cons, List.sum_cons, add_left_comm, ih,
      add_left_comm, ← add_assoc, htr.add_pre, add_assoc]

/-- A firing sequence returns to its starting marking exactly when the fired transitions consume
as many tokens as they produce, in every place. -/
theorem mTr_eq_iff_sum_pre_eq {M M' : Marking Place} {ts : List Transition}
    (h : N.lts.MTr M ts M') : M' = M ↔ (ts.map N.pre).sum = (ts.map N.post).sum := by
  have heq := mTr_add_sum_pre h
  constructor
  · rintro rfl
    exact add_left_cancel heq
  · intro h0
    rw [h0] at heq
    exact add_right_cancel heq

section Int

variable [DecidableEq Place]

/-- View a marking as an integer vector. -/
def Marking.toInt : Marking Place →+ (Place → ℤ) :=
  AddMonoidHom.pi fun p => (Nat.castAddMonoidHom ℤ).comp (Multiset.countAddMonoidHom p)

@[simp] theorem Marking.toInt_apply (M : Marking Place) (p : Place) :
    Marking.toInt M p = M.count p :=
  rfl

theorem Marking.toInt_injective : Function.Injective (Marking.toInt (Place := Place)) :=
  fun _ _ h => Multiset.ext.2 fun p => by simpa using congrFun h p

variable (N) in
/-- The effect of firing `t`: tokens produced minus tokens consumed. -/
def incidence (t : Transition) : Place → ℤ :=
  Marking.toInt (t •[N]) - Marking.toInt (•[N] t)

variable (N) in
/-- The total effect of a firing sequence. -/
def effect (ts : List Transition) : Place → ℤ :=
  (ts.map N.incidence).sum

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

end Int

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
